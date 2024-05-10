# Copyright 2023-2024, Galois Inc. All rights reserved.

from __future__ import annotations
import io
import os.path
import re
from difflib import HtmlDiff
from threading import Thread, Condition
from typing import Optional

from binaryninja import execute_on_main_thread_and_wait, BinaryView, interaction, \
    DisassemblyTextLine, Architecture, load, Settings
from binaryninja.enums import BranchType, HighlightStandardColor, ThemeColor
from binaryninja import InstructionTextToken as ITT
from binaryninja.enums import InstructionTextTokenType as ITTType
from binaryninja.flowgraph import FlowGraph, FlowGraphNode, FlowGraphEdge, EdgeStyle
from binaryninjaui import UIAction, UIActionHandler, Menu, UIActionContext, FlowGraphWidget, \
    FileContext, UIContext, ViewFrame, ViewLocation

# PySide6 import MUST be after import of binaryninjaui
from PySide6.QtCore import Qt, QCoreApplication
from PySide6.QtGui import QMouseEvent, QAction
from PySide6.QtWidgets import QHBoxLayout, QLabel, QVBoxLayout, QLineEdit, QPlainTextEdit, QDialog, QWidget, \
    QSplitter, QMenu, QTextEdit

from .mcad.PateMcad import PateMcad, CycleCount
from . import pate


class PateWidget(QWidget):
    context: UIContext | None
    config: dict
    pate_thread: PateThread | None
    flow_graph_widget: MyFlowGraphWidget

    def __init__(self, context: UIContext, parent: QWidget) -> None:
        super().__init__(parent)

        # TODO: Should not store this, I think there is one per top level window and they can come and go.
        self.context = context

        self.pate_thread = None

        self.flow_graph_widget = MyFlowGraphWidget(self, self)

        self.output_field = QPlainTextEdit()
        self.output_field.setReadOnly(True)
        self.output_field.setMaximumBlockCount(1000000)

        self.cmd_field = QLineEdit()
        self.cmd_field.setEnabled(False)
        self.cmd_field.returnPressed.connect(self.onPateCommandReturnPressed)

        cmd_field_layout = QHBoxLayout()
        cmd_field_layout.addWidget(QLabel("PATE Command: "))
        cmd_field_layout.addWidget(self.cmd_field)
        cmd_field_layout.setAlignment(Qt.AlignmentFlag.AlignCenter)

        io_layout = QVBoxLayout()
        io_layout.addWidget(self.output_field)
        io_layout.addLayout(cmd_field_layout)

        io_widget = QWidget()
        io_widget.setLayout(io_layout)

        splitter = QSplitter()
        splitter.setOrientation(Qt.Orientation.Vertical)
        splitter.addWidget(self.flow_graph_widget)
        splitter.addWidget(io_widget)

        main_layout = QHBoxLayout()
        main_layout.addWidget(splitter)
        self.setLayout(main_layout)

        self.user_response_condition = Condition()
        self.user_response = None

        self.originalFilename = None
        self.patchedFilename = None

    def loadBinaryFileTabs(self, config: dict):
        #print('config:', config)
        cwd = config.get('cwd')
        original = config.get('original')
        patched = config.get('patched')
        if cwd and original:
            self.originalFilename = os.path.join(cwd, original)
        if cwd and patched:
            self.patchedFilename = os.path.join(cwd, patched)
        if self.originalFilename:
            getTabForFilename(self.context, self.originalFilename, True)
        if self.patchedFilename:
            getTabForFilename(self.context, self.patchedFilename, True)

    def getOriginalBinaryView(self):
        if self.originalFilename:
            # TODO: Really need to make sure analysis completes befoer usage, but thread issues make this difficult
            return getElfBinaryViewForFilename(self.context, self.originalFilename)
            #self.originalBinaryView = load(self.originalFilename)
            #self.originalBinaryView.update_analysis_and_wait()

    def getPatchedBinaryView(self):
        if self.patchedFilename:
            # TODO: Really need to make sure analysis completes befoer usage, but thread issues make this difficult
            return getElfBinaryViewForFilename(self.context, self.patchedFilename)
            #self.patchedBinaryView = load(self.patchedFilename)
            #self.patchedBinaryView.update_analysis_and_wait()

    def gotoOriginalAddress(self, addr: int):
        showLocationInFilename(self.context, self.originalFilename, addr)

    def gotoPatchedAddress(self, addr: int):
        showLocationInFilename(self.context, self.patchedFilename, addr)

    def closeEvent(self, event):
        # TODO: This is not called when the parent tab is closed.
        print("Close Event PateWidget:", self)
        if self.pate_thread:
            self.pate_thread.cancel()

    # def tabCloseRequested(self, index):
    #     # TODO: Problem: Since we don't have the DockableTabWidget we cannot tell if index refers to the tab
    #     #  associated with this PateWidget.
    #     print("Handle Tab Close PateWidget:", self, "index:", index)

    def onPateCommandReturnPressed(self):
        user_response = self.cmd_field.text()
        # TODO: validate here or use QLineEdit validation mechanism
        self.cmd_field.setText('Pate running...')
        self.cmd_field.setEnabled(False)
        # Notify Pate background thread
        with self.user_response_condition:
            self.user_response = user_response
            self.user_response_condition.notify()

    def ask_user(self, prompt: str, choices: list[str], replay: bool):
        query = '\n' + prompt
        for i, e in enumerate(choices):
            query += '\n  {}'.format(e)
        self.output_field.appendPlainText(query)
        self.cmd_field.setText('')
        self.cmd_field.setEnabled(True)
        self.cmd_field.setFocus()

    def injectBinjaDissembly(self, original_lines, patched_lines):

        obv = self.getOriginalBinaryView()
        original_lines = list(map(lambda line: subDisassemblyForInstAddr(line, obv), original_lines))

        pbv = self.getPatchedBinaryView()
        patched_lines = list(map(lambda line: subDisassemblyForInstAddr(line, pbv), patched_lines))

        return original_lines, patched_lines

    def mcad_annotate_inst_tree(self, inst_tree: Optional[dict], bv: BinaryView):
        """Add MCAD cycle counts to instruction tree. NOOP if cycle counts all ready exist."""
        if not inst_tree:
            return

        # TODO: Config paramater to enabel/disable MCAD intigration

        # Look at first instruction to determine arch. We assume all instructions in prefix are same arch.
        if inst_tree['prefix']:
            instAddr = inst_tree['prefix'][0]
            if instAddr.get('cycleCount'):
                # We already got the cycle counts for this instruction tree.
                return
            offset = int(instAddr['address']['offset'], 16)
            arch = getInstArch(offset, bv)
            mcadServer = PateMcad.getServerForArch(arch.name)
            if not mcadServer:
                # Could not start MCAD server for arch
                return

        # Get the list of instruction bytes for the block
        instructions = []
        for instAddr in inst_tree['prefix']:
            # TODO: Ignore base for now. Ask Dan about this.
            # base = int(instAddr['address']['base'], 16?)
            offset = int(instAddr['address']['offset'], 16)
            instLen = bv.get_instruction_length(offset, arch)
            if instLen == 0:
                break
            instBytes = bv.read(offset, instLen)
            # disassembly = bv.get_disassembly(offset, arch)
            # print('offset:', offset)
            # print('len:', instLen)
            # print('bytes:', instBytes)
            # print('disassembly:', disassembly)
            instructions.append(instBytes)

        if instructions:
            # Get the cycle counts from MCAD
            # TODO: Check for gRPC error
            # print('arch', arch)
            # print('instructions', instructions)
            cycleCounts = mcadServer.request_cycle_counts(instructions)
            # print('cycleCounts', cycleCounts)

            if cycleCounts:
                # Annotate the instruction tree with cycle counts
                for (instAddr, cycleCount) in zip(inst_tree['prefix'], cycleCounts):
                    instAddr['cycleCount'] = cycleCount

        # Process the children. Note: true/false are not necessarily accurate.
        self.mcad_annotate_inst_tree(inst_tree['suffix_true'], bv)
        self.mcad_annotate_inst_tree(inst_tree['suffix_false'], bv)


class GuiUserInteraction(pate.PateUserInteraction):
    def __init__(self, pate_widget: PateWidget):
        self.pate_widget = pate_widget

    def ask_user(self, prompt: str, choices: list[str], replay_choice: Optional[str] = None) -> Optional[str]:
        execute_on_main_thread_and_wait(lambda: self.pate_widget.ask_user(prompt, choices, replay_choice is not None))
        if replay_choice:
            execute_on_main_thread_and_wait(lambda: self.pate_widget.cmd_field.setText(replay_choice + ' (replay)'))
        #Wait for user to respond to prompt. This happens on the GUI thread.
        urc = self.pate_widget.user_response_condition
        with urc:
            while self.pate_widget.user_response is None:
                urc.wait()
            choice = self.pate_widget.user_response
            self.pate_widget.user_response = None
        if replay_choice:
            execute_on_main_thread_and_wait(lambda: self.pate_widget.output_field.appendPlainText(f'PATE Command: {replay_choice} (replay)\n'))
            return replay_choice
        else:
            execute_on_main_thread_and_wait( lambda: self.pate_widget.output_field.appendPlainText(f'PATE Command: {choice}\n'))
            return choice

    def show_message(self, msg: str) -> None:
        execute_on_main_thread_and_wait(lambda: self.pate_widget.output_field.appendPlainText(msg))

    def show_cfar_graph(self, graph: pate.CFARGraph) -> None:
        execute_on_main_thread_and_wait(lambda: self.pate_widget.flow_graph_widget.build_pate_flow_graph(graph))

        promptNode = graph.getPromptNode()
        eqCondNodes = graph.getEqCondNodes()
        if promptNode:
            self.pate_widget.flow_graph_widget.flowGraph.layout_and_wait()
            execute_on_main_thread_and_wait(lambda: self.pate_widget.flow_graph_widget.showCfars([promptNode]))
        elif eqCondNodes:
            self.pate_widget.flow_graph_widget.flowGraph.layout_and_wait()
            execute_on_main_thread_and_wait(lambda: self.pate_widget.flow_graph_widget.showCfars(eqCondNodes))


class PateThread(Thread):

    # TODO: Look at interaction.run_progress_dialog
    # handle cancel and restart
    def __init__(self,
                 filename,
                 pate_widget: PateWidget,
                 ):
        super().__init__(name="Pate " + filename)
        self.daemon = True
        self.filename = filename
        self.pate_widget = pate_widget
        self.pate_user = GuiUserInteraction(self.pate_widget)
        self.pate_wrapper = pate.PateWrapper(self.filename,
                                             self.pate_user,
                                             config_callback=lambda c: self._config_callback(c))

    def _config_callback(self, config: dict):
        execute_on_main_thread_and_wait(
            lambda: self.pate_widget.loadBinaryFileTabs(config))
        execute_on_main_thread_and_wait(
            lambda: self.pate_widget.context.createTabForWidget("PATE " + os.path.basename(self.filename),
                                                                self.pate_widget))

        # Hack to pre-start MCAD server(s)
        bv = self.pate_widget.getOriginalBinaryView()
        arch = bv.arch
        if arch.name in ['thumb2', 'armv7']:
            PateMcad.getServerForArch('thumb2')
            PateMcad.getServerForArch('armv7')

        # TODO: This is does not quite work. Several problems:
        # - tabCloseRequests is called for every tab, not just the PateWidget tab
        # - When tabs are moved, a new DockableTabWidget is crated taht will no have this signal connected.
        # - When PateWidgit.tabCloeRequested is called, there is no ref to the DockableTabWidget
        #ptw: DockableTabWidget = getAncestorInstanceOf(self.pate_widget, DockableTabWidget)
        #print('TabWidget:', ptw)
        #ptw.tabCloseRequested.connect(self.pate_widget.tabCloseRequested)

    def run(self):
        #self.progress = 'Pate running...'
        execute_on_main_thread_and_wait(lambda: self.pate_widget.cmd_field.setText('Pate running...'))
        self.pate_wrapper.run()
        execute_on_main_thread_and_wait(lambda: self.pate_widget.cmd_field.setText('Pate finished'))

    def cancel(self) -> None:
        if self.pate_wrapper:
            self.pate_wrapper.cancel()

# def run_pate_thread_nov23_t4_dendy1011(bv):
#     # x = pate.run_may23_c10(self.replay)
#     # x = pate.run_nov23_t1_self(self.replay)
#     # x = pate.run_nov23_t1_room1018(self.replay)
#     # x = pate.run_nov23_t3_self(self.replay)
#     # x = pate.run_nov23_t4_self(self.replay)
#     # x = pate.run_nov23_t4_master(self.replay)
#     # x = pate.run_nov23_t4_dendy1011(self.replay)
#     pt = PateThread(bv, pate.run_nov23_t4_rm1011_dendy, True)
#     pt.start()
#
#
# def run_pate_thread_may23_ch10(bv):
#     pt = PateThread(bv, pate.run_may23_c10, False)
#     pt.start()
#
#
# def run_pate_thread_nov23_t1_room1018(bv):
#     pt = PateThread(bv, pate.run_nov23_t1_rm1018, False)
#     pt.start()


class TraceWidget(QWidget):
    def __init__(self, parent):
        super().__init__(parent)

        self.domainField = QPlainTextEdit()
        self.domainField.setReadOnly(True)
        self.domainField.setMaximumBlockCount(1000)

        self.traceDiffField = QTextEdit()
        self.traceDiffField.setReadOnly(True)
        self.traceDiffField.setFont({"Courier"});

        vsplitter = QSplitter()
        vsplitter.setOrientation(Qt.Orientation.Vertical)
        vsplitter.addWidget(self.domainField)
        vsplitter.addWidget(self.traceDiffField)

        main_layout = QHBoxLayout()
        main_layout.addWidget(vsplitter)
        self.setLayout(main_layout)

    def setTrace(self, trace: dict, label: str = None):
        with io.StringIO() as out:
            pate.pprint_node_event_trace_domain(trace, out=out)
            self.domainField.setPlainText(out.getvalue())

        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)

        hasOriginalTrace: bool = 'original' in trace.get('traces', {})
        hasPatchedTrace: bool = 'patched' in trace.get('traces', {})

        originalLines = []
        with io.StringIO() as out:
            pate.pprint_node_event_trace_original(trace, out=out)
            originalLines = out.getvalue().splitlines()

        patchedLines = []
        with io.StringIO() as out:
            pate.pprint_node_event_trace_patched(trace, out=out)
            patchedLines = out.getvalue().splitlines()

        # Replace addr lines with binja disassembly
        if pw:
            originalLines, patchedLines = pw.injectBinjaDissembly(originalLines, patchedLines)

        if hasOriginalTrace and hasPatchedTrace:
            # Both, show diff
            html = generateHtmlDiff(originalLines, patchedLines, label)
            self.traceDiffField.setHtml(html)
        elif hasOriginalTrace:
            # Only original
            self.traceDiffField.setText('\n'.join(originalLines))
        else:
            # Only patched
            self.traceDiffField.setText('\n'.join(patchedLines))



class PateCfarExitDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.resize(1100, 600)
        self.setWindowTitle("Exit Trace")

        self.traceWidget = TraceWidget(self)

        main_layout = QHBoxLayout()
        main_layout.addWidget(self.traceWidget)
        self.setLayout(main_layout)

    def setTrace(self, trace: dict, label: str = None):
        self.traceWidget.setTrace(trace, label)


class PateCfarEqCondDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.resize(1500, 800)

        self.setWindowTitle("Equivalence Condition")

        # Equivalence Condition Box
        self.eqCondField = QPlainTextEdit()
        self.eqCondField.setReadOnly(True)
        self.eqCondField.setMaximumBlockCount(1000)
        eqCondBoxLayout = QVBoxLayout()
        eqCondBoxLayout.addWidget(QLabel("Programs behave equivalently when:"))
        eqCondBoxLayout.addWidget(self.eqCondField)
        eqCondBox = QWidget()
        eqCondBox.setLayout(eqCondBoxLayout)

        # True Trace Box
        self.trueTraceWidget = TraceWidget(self)
        trueTraceBoxLayout = QVBoxLayout()
        trueTraceBoxLayout.addWidget(QLabel("Trace showing EQUIVALENT behaviour:"))
        trueTraceBoxLayout.addWidget(self.trueTraceWidget)
        trueTraceBox = QWidget()
        trueTraceBox.setLayout(trueTraceBoxLayout)

        # False Trace Box
        self.falseTraceWidget = TraceWidget(self)
        falseTraceBoxLayout = QVBoxLayout()
        falseTraceBoxLayout.addWidget(QLabel("Trace showing DIFFERENT behaviour:"))
        falseTraceBoxLayout.addWidget(self.falseTraceWidget)
        falseTraceBox = QWidget()
        falseTraceBox.setLayout(falseTraceBoxLayout)

        # True/False Splitter (horizontal)
        trueFalseSplitter = QSplitter()
        trueFalseSplitter.setOrientation(Qt.Orientation.Horizontal)
        trueFalseSplitter.addWidget(trueTraceBox)
        trueFalseSplitter.addWidget(falseTraceBox)

        # Main Splitter (vertical)
        mainSplitter = QSplitter()
        mainSplitter.setOrientation(Qt.Orientation.Vertical)
        mainSplitter.addWidget(eqCondBox)
        mainSplitter.addWidget(trueFalseSplitter)

        # Main Layout
        main_layout = QHBoxLayout()
        main_layout.addWidget(mainSplitter)
        self.setLayout(main_layout)

    def setTrueTrace(self, trace: dict, label: str = None):
        self.trueTraceWidget.setTrace(trace, label)

    def setFalseTrace(self, trace: dict, label: str = None):
        self.falseTraceWidget.setTrace(trace, label)


class InstTreeDiffWidget(QWidget):
    def __init__(self, parent):
        super().__init__(parent)

        self.instDiffField = QTextEdit()
        self.instDiffField.setReadOnly(True)
        self.instDiffField.setFont({"Courier"});

        main_layout = QHBoxLayout()
        main_layout.addWidget(self.instDiffField)
        self.setLayout(main_layout)

    def setInstTrees(self, instTrees: dict, label: str = None):
        if not instTrees:
            self.instDiffField.append("No Instruction Trees")
            return

        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)

        hasOriginalInstTree: bool = 'original' in instTrees
        hasPatchedInstTree: bool = 'patched' in instTrees

        originalLines = []
        if instTrees.get('original'):
            originalInstTree = instTrees['original']
            obv = pw.getOriginalBinaryView()
            pw.mcad_annotate_inst_tree(originalInstTree, obv)
            originalLines = self.getInstTreeLines(originalInstTree, obv)

        patchedLines = []
        if instTrees.get('patched'):
            patchedInstTree = instTrees['patched']
            pbv = pw.getPatchedBinaryView()
            pw.mcad_annotate_inst_tree(patchedInstTree, pbv)
            patchedLines = self.getInstTreeLines(patchedInstTree, pbv)

        if hasOriginalInstTree and hasPatchedInstTree:
            # Both, show diff
            html = generateHtmlDiff(originalLines, patchedLines, label)
            self.instDiffField.setHtml(html)
        elif hasOriginalInstTree:
            # Only original
            self.instDiffField.setPlainText('\n'.join(originalLines))
        else:
            # Only patched
            self.instDiffField.setPlainText('\n'.join(patchedLines))

    def getInstTreeLines(self, instTree, bv, pre: str = '', cumu: int = 0):

        if not instTree:
            return []

        prefixLines = []
        for instAddr in instTree['prefix']:
            line = ''
            if instAddr.get('cycleCount'):
                cc: CycleCount = instAddr['cycleCount']
                cycles = cc.executed - cc.ready
                cumu += cycles
                line += f'{cycles:2d}'
                if cc.is_under_pressure:
                    line += '!'
                else:
                    line += ' '
                line += f' {cumu:4d}'
            #else:
            #    line += ' ' * 8

            # TODO: Ignore base for now. Ask Dan about this.
            # base = int(instAddr['address']['base'], 16?)
            offset = int(instAddr['address']['offset'], 16)
            arch = getInstArch(offset, bv)
            disassembly = next(bv.disassembly_text(offset, arch), ['??????'])[0]
            line += f' {pre}{offset:08x} {disassembly}'

            prefixLines.append(line)

        # Process the children. Note: true/false are not necessarily accurate.
        trueBranchLines = self.getInstTreeLines(instTree['suffix_true'], bv, pre + '+', cumu)
        falseBranchLines = self.getInstTreeLines(instTree['suffix_false'], bv, pre + '-', cumu)

        return prefixLines + trueBranchLines + falseBranchLines


class InstTreeGraphWidget(FlowGraphWidget):

    def __init__(self, parent: QWidget, view: BinaryView = None, graph: FlowGraph=None):
        super().__init__(parent, view, graph)

        # Disable context menu. We need a QMouseEvent to get nodes and edges at mose position, so we use
        # mouse press event instead.
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.NoContextMenu)

    def setInstTree(self, instTree: dict):
        if not instTree:
            return

        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)
        pw.mcad_annotate_inst_tree(instTree, self.getData())

        _flowGraph = FlowGraph()
        self._buildGraph(instTree, _flowGraph)
        self.setGraph(_flowGraph)

    def _buildGraph(self, instTree: dict,
                    flowGraph: FlowGraph,
                    parent: FlowGraphNode = None,
                    cumu: int = 0):
        if not instTree:
            return

        bv: BinaryView = self.getData()
        prefixLines = []
        for instAddr in instTree['prefix']:
            tokens = []
            if instAddr.get('cycleCount'):
                cc: CycleCount = instAddr['cycleCount']
                cycles = cc.executed - cc.ready
                cumu += cycles
                cyclesStr = f'{cycles:2d}'
                if cc.is_under_pressure:
                    cyclesStr += '!'
                else:
                    cyclesStr += ' '
                tokens.append(ITT(ITTType.TextToken, cyclesStr))
                tokens.append(ITT(ITTType.TextToken, f' {cumu:4d}'))
            #else:
            #    tokens.append(ITT(ITTType.TextToken, ' ' * 8))

            tokens.append(ITT(ITTType.TextToken, ' '))

            # TODO: Ignore base for now. Ask Dan about this.
            # base = int(instAddr['address']['base'], 16?)
            offset = int(instAddr['address']['offset'], 16)
            tokens.append(ITT(ITTType.AddressDisplayToken, f'{offset:08x}'))

            tokens.append(ITT(ITTType.TextToken, ' '))

            arch = getInstArch(offset, bv)

            # #disassembly = next(bv.disassembly_text(offset, arch), ['??????'])[0]
            # disassembly = bv.get_disassembly(offset, arch)
            # if not disassembly:
            #     disassembly = '??????'
            # tokens.append(ITT(ITTType.TextToken, disassembly))
            # print("Disassembly:", disassembly)

            disassemblyTokens = next(bv.disassembly_tokens(offset, arch), None)
            if disassemblyTokens:
                disassembly = disassemblyTokens[0]
                for token in disassembly:
                    if token.type != ITTType.TagToken:
                        tokens.append(token)

            prefixLines.append(DisassemblyTextLine(tokens, offset))

        flowNode = FlowGraphNode(flowGraph)
        flowNode.lines = prefixLines
        flowGraph.append(flowNode)

        # EDGE
        if parent:
            edgeStyle = EdgeStyle(width=1, theme_color=ThemeColor.GraphNodeOutlineColor)
            parent.add_outgoing_edge(BranchType.UserDefinedBranch, flowNode, edgeStyle)

        # Process the children. Note: true/false are not necessarily accurate.
        self._buildGraph(instTree['suffix_true'], flowGraph, flowNode, cumu)
        self._buildGraph(instTree['suffix_false'], flowGraph, flowNode, cumu)


class PateCfarInstTreeDialog(QDialog):
    def __init__(self, instTrees: dict, label: str = None, parent=None):
        super().__init__(parent)
        self.resize(1100, 600)
        self.setWindowTitle(f'Instruction Trees - {label}')

        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)

        # Original Graph Box
        if instTrees.get('original'):
            obv = pw.getOriginalBinaryView()
            self.originalInstTreeGraphWidget = InstTreeGraphWidget(self, obv)
            self.originalInstTreeGraphWidget.setInstTree(instTrees['original'])
            originalBoxLayout = QVBoxLayout()
            originalBoxLayout.addWidget(QLabel("Original"))
            originalBoxLayout.addWidget(self.originalInstTreeGraphWidget)
            originalBox = QWidget()
            originalBox.setLayout(originalBoxLayout)

        # Patched Graph Box
        if instTrees.get('patched'):
            pbv = pw.getPatchedBinaryView()
            self.patchedInstTreeGraphWidget = InstTreeGraphWidget(self, pbv)
            self.patchedInstTreeGraphWidget.setInstTree(instTrees['patched'])
            patchedBoxLayout = QVBoxLayout()
            patchedBoxLayout.addWidget(QLabel("Patched"))
            patchedBoxLayout.addWidget(self.patchedInstTreeGraphWidget)
            patchedBox = QWidget()
            patchedBox.setLayout(patchedBoxLayout)

        # Graph Box - Original or Patched or Splitter (horizontal)
        if instTrees.get('original') and instTrees.get('patched'):
            treeGraphBox = QSplitter()
            treeGraphBox.setOrientation(Qt.Orientation.Horizontal)
            treeGraphBox.addWidget(originalBox)
            treeGraphBox.addWidget(patchedBox)
            # Text Diff Widget
            self.instTreeDiffWidget = InstTreeDiffWidget(self)
            self.instTreeDiffWidget.setInstTrees(instTrees, label)

            # Main Splitter (vertical)
            mainSplitter = QSplitter()
            mainSplitter.setOrientation(Qt.Orientation.Vertical)
            mainSplitter.addWidget(treeGraphBox)
            mainSplitter.addWidget(self.instTreeDiffWidget)

        elif instTrees.get('original'):
            mainSplitter = originalBox
        else:
            mainSplitter = patchedBox

        # Main Layout
        mainLayout = QHBoxLayout()
        mainLayout.addWidget(mainSplitter)
        self.setLayout(mainLayout)


class MyFlowGraphWidget(FlowGraphWidget):

    pate_widget: PateWidget
    flowGraph: FlowGraph
    cfarGraph: pate.CFARGraph
    flowToCfar: dict[FlowGraphNode, pate.CFARNode]
    cfarToFlow: dict[pate.CFARNode, FlowGraphNode]

    def __init__(self, parent: QWidget, pate_widget: PateWidget, view: BinaryView=None, graph: FlowGraph=None):
        super().__init__(parent, view, graph)
        self.pate_widget = pate_widget

        # Disable context menu. We need a QMouseEvent to get nodes and edges at mose position, so we use
        # mouse press event instead.
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.NoContextMenu)

    def build_pate_flow_graph(self, cfarGraph: pate.CFARGraph):
        self.flowGraph = FlowGraph()
        self.cfarGraph = cfarGraph

        self.flowToCfar = {}
        self.cfarToFlow = {}

        # First create all nodes
        cfar_node: pate.CFARNode
        for cfar_node in self.cfarGraph.nodes.values():
            flow_node = FlowGraphNode(self.flowGraph)

            self.flowToCfar[flow_node] = cfar_node

            out = io.StringIO()

            out.write(cfar_node.id.replace(' <- ', '\n  <- '))
            out.write('\n')

            cfar_node.pprint_node_contents('', out)

            lines = out.getvalue().split('\n')
            truncLines = []
            maxLen = 0
            for line in lines:
                if len(truncLines) <= 1:
                    # First and second line
                    maxLen = max(maxLen, len(line))
                else:
                    # Truncate rest to length of first
                    if len(line) > maxLen:
                        line = line[:maxLen-4] + ' ...'
                truncLines.append(line)

            flow_node.lines = truncLines
            # flow_node.lines = [lines[0]]

            if cfar_node.id.find(' vs ') >= 0:
                # Per discussion with Dan, it does not make sense to highlight these.
                # flow_node.highlight = HighlightStandardColor.BlueHighlightColor
                pass
            elif cfar_node.id.find('(original') >= 0:
                flow_node.highlight = HighlightStandardColor.GreenHighlightColor
            elif cfar_node.id.find('(patched)') >= 0:
                flow_node.highlight = HighlightStandardColor.MagentaHighlightColor

            self.flowGraph.append(flow_node)
            self.cfarToFlow[cfar_node.id] = flow_node

        # Add edges
        cfar_node: pate.CFARNode
        for cfar_node in self.cfarGraph.nodes.values():
            flow_node = self.cfarToFlow[cfar_node.id]
            cfar_exit: pate.CFARNode
            for cfar_exit in cfar_node.exits:
                flow_exit = self.cfarToFlow[cfar_exit.id]
                if self.showCfarExitInfo(cfar_node, cfar_exit, simulate=True):
                    edgeStyle = EdgeStyle(width=1, theme_color=ThemeColor.RedStandardHighlightColor)
                else:
                    edgeStyle = EdgeStyle(width=1, theme_color=ThemeColor.GraphNodeOutlineColor)
                flow_node.add_outgoing_edge(BranchType.UserDefinedBranch, flow_exit, edgeStyle)

        self.setGraph(self.flowGraph)

    def showCfars(self, cfars: list[pate.CFARNode]):
        focusFlow = None
        for cfar in cfars:
            flow_node = self.cfarToFlow.get(cfar.id)
            flow_node.highlight = HighlightStandardColor.RedHighlightColor
            if not focusFlow:
                focusFlow = flow_node
        #print('focusCfar.id', focusCfar.id)
        #print('focusFlowNode', focusFlow)
        if focusFlow:
            self.showNode(focusFlow)

    def mousePressEvent(self, event: QMouseEvent):
        if event.button() == Qt.RightButton:
            node = self.getNodeForMouseEvent(event)
            edgeTuple = self.getEdgeForMouseEvent(event)
            # if node:
            #     print("Node: ", self.flowToCfarNode[node].id)
            # if edgeTuple:
            #     print("Edge source: ", self.flowToCfarNode[edgeTuple[0].source].id)
            #     print("Edge target: ", self.flowToCfarNode[edgeTuple[0].target].id)
            #     print("Edge incoming: ", edgeTuple[1])

            if node:
                self.nodePopupMenu(event, node)

            elif edgeTuple:
                self.edgePopupMenu(event, edgeTuple)
        else:
            super().mousePressEvent(event)

    def nodePopupMenu(self, event: QMouseEvent, node: FlowGraphNode):

        cfarNode = self.flowToCfar[node]

        if cfarNode:

            menu = QMenu(self)

            if cfarNode.original_addr:
                action = QAction(f'Goto original address {hex(cfarNode.original_addr)}', self)
                action.triggered.connect(lambda _: self.pate_widget.gotoOriginalAddress(cfarNode.original_addr))
                menu.addAction(action)

            if cfarNode.patched_addr:
                action = QAction(f'Goto patched address {hex(cfarNode.patched_addr)}', self)
                action.triggered.connect(lambda _: self.pate_widget.gotoPatchedAddress(cfarNode.patched_addr))
                menu.addAction(action)

            if cfarNode.predicate:
                action = QAction('Show Equivalence Condition', self)
                action.triggered.connect(lambda _: self.showCfarEqCondDialog(cfarNode))
                menu.addAction(action)

            if cfarNode.instruction_trees:
                action = QAction('Show Instruction Trees', self)
                action.triggered.connect(lambda _: self.showInstTreeInfo(cfarNode.instruction_trees,
                                                                         cfarNode.id))
                menu.addAction(action)

            if menu.actions():
                menu.exec_(event.globalPos())

    def showCfarEqCondDialog(self, cfarNode: pate.CFARNode):
        d = PateCfarEqCondDialog(parent=self)
        d.setWindowTitle(f'{d.windowTitle()} - {cfarNode.id}')
        with io.StringIO() as out:
            pate.pprint_symbolic(out, cfarNode.predicate)
            d.eqCondField.appendPlainText(out.getvalue())
        d.setTrueTrace(cfarNode.trace_true)
        d.setFalseTrace(cfarNode.trace_false)
        d.exec()

    def edgePopupMenu(self, event: QMouseEvent, edgeTuple: tuple[FlowGraphEdge, bool]):
        edge = edgeTuple[0]
        incoming = edgeTuple[1]  # Direction of edge depends on which half was clicked
        if incoming:
            sourceCfarNode = self.flowToCfar[edge.target]
            exitCfarNode = self.flowToCfar[edge.source]
        else:
            sourceCfarNode = self.flowToCfar[edge.source]
            exitCfarNode = self.flowToCfar[edge.target]

        if sourceCfarNode and exitCfarNode:

            exitMetaData = sourceCfarNode.exit_meta_data.get(exitCfarNode, {})

            menu = QMenu(self)

            if self.showCfarExitInfo(sourceCfarNode, exitCfarNode, True):
                action = QAction(f'Show Exit Trace', self)
                action.triggered.connect(lambda _: self.showCfarExitInfo(sourceCfarNode, exitCfarNode))
                menu.addAction(action)

            if exitMetaData.get('instruction_trees_to_exit'):
                action = QAction(f'Show Exit Instruction Trees', self)
                action.triggered.connect(lambda _: self.showInstTreeInfo(exitMetaData['instruction_trees_to_exit'],
                                                                         sourceCfarNode.id + " to exit " + exitCfarNode.id))
                menu.addAction(action)

            if menu.actions():
                menu.exec_(event.globalPos())

    def showCfarExitInfo(self, sourceCfarNode: pate.CFARNode, exitCfarNode: pate.CFARNode, simulate: bool=False) -> bool:

        exitMetaData = sourceCfarNode.exit_meta_data.get(exitCfarNode, {})

        ceTrace = exitMetaData.get('ce_event_trace')
        trace = exitMetaData.get('event_trace')
        if ceTrace:
            if not simulate:
                self.showExitTraceInfo(sourceCfarNode, exitCfarNode, ceTrace, 'Counter-Example Trace')
            return True
        elif trace:
            if not simulate:
                self.showExitTraceInfo(sourceCfarNode, exitCfarNode, trace, 'Witness Trace')
            return True
        else:
            # TODO: dialog?
            return False

    def showExitTraceInfo(self, sourceCfarNode: pate.CFARNode,
                          exitCfarNode: pate.CFARNode,
                          trace: dict,
                          label: str = None):
        d = PateCfarExitDialog(self)
        d.setWindowTitle(f'{d.windowTitle()} - {sourceCfarNode.id} exit to {exitCfarNode.id}')
        d.setTrace(trace, label)
        d.exec()

    def showInstTreeInfo(self, instTrees: dict, label: str):
        d = PateCfarInstTreeDialog(instTrees, label=label, parent=self)
        d.show()


def generateHtmlDiff(originalLines: list[str], patchedLines: list[str], label: str = None) -> str:
    if label:
        fromdesc = f'{label} (original)'
        todesc = f'{label} (patched)'
    else:
        fromdesc = f'Original'
        todesc = f'Patched'

    htmlDiff = HtmlDiff()
    return htmlDiff.make_file(originalLines, patchedLines, fromdesc=fromdesc, todesc=todesc)


def getInstArch(addr: int, bv: BinaryView) -> Architecture:
    flist = bv.get_functions_containing(addr)
    if flist:
        # Just use first function
        f = flist[0]
        arch = f.arch
    else:
        # No function found, use file arch
        arch = bv.arch
    return arch


# Pattern to match a pate address
pateInstAddrPattern = re.compile(r'(.*)S[0-9A-Fa-f]+\+(0x[0-9A-Fa-f]+)$')


def subDisassemblyForInstAddr(line, bv):
    def subDisassemblyForMatch(m):
        pre = m.group(1)
        a = int(m.group(2), 16)
        # Note: bv is available via lexical scope
        arch = getInstArch(a, bv)
        inst = next(bv.disassembly_text(a, arch))[0]
        return pre + str(hex(a)) + " " + inst

    return re.sub(pateInstAddrPattern, subDisassemblyForMatch, line)

def getTabForFilename(context: UIContext, filename: str, loadIfDoesNotExist: bool = True) -> Optional[QWidget]:
    """Find Tab for filename."""
    tab = None
    c: UIContext
    for c in UIContext.allContexts():
        for t in c.getTabs():
            vf: ViewFrame = context.getViewFrameForTab(t)
            if vf:
                fc: FileContext = vf.getFileContext()
                #print('tab:', t, "ViewFrame", vf, "filename:", fc.getFilename())
                if fc.getFilename() == filename:
                    tab = t
    if not tab and loadIfDoesNotExist:
        # No Tab found for filename, open it in a new tab
        file_context = context.openFilename(filename)
        #view_frame = context.openFileContext(file_context)
        tab = getTabForFilename(context, filename, False)
        #print('Opened ViewFrame:', view_frame, "Tab:", tab)
    #print('Found Tab:', tab, "for filename:", filename, 'and bv: ', bv)
    return tab


def getElfBinaryViewForTab(context: UIContext, tab: QWidget) -> Optional[BinaryView]:
    vf: ViewFrame = context.getViewFrameForTab(tab)
    if vf:
        v = vf.getViewForType('Linear:ELF')
        if v:
            return v.getData()


def getElfBinaryViewForFilename(context: UIContext, filename: str) -> Optional[BinaryView]:
    t = getTabForFilename(context, filename, True)
    if t:
        return getElfBinaryViewForTab(context, t)


def showLocationInFilename(context: UIContext, filename: str, addr: int):
    if filename:
        # Get tab for filename, opening if necessary
        tab = getTabForFilename(context, filename, True)
        vl = ViewLocation("What is this for?", addr)
        vf: ViewFrame = context.getViewFrameForTab(tab)
        vf.navigateToViewLocation(vf.getCurrentBinaryView(), vl)
        #vf.focus()
        #vf.setFocus()
        context.activateTab(tab)
        #print("Showed location", addr, "in", filename)


def getAncestorInstanceOf(w: QWidget, c: type) -> Optional[QWidget]:
    p = w.parent()
    #print('parent:', p)
    if p is None:
        return None
    elif isinstance(p, c):
        return p
    else:
        return getAncestorInstanceOf(p, c)


def launch_pate(context: UIActionContext):

    f = interaction.get_open_filename_input(
        "Run PATE",
        "PATE Run Configuration (*.run-config.json);;PATE Replay (*.replay)")

    if f is None:
        return

    pate_widget = PateWidget(context.context, context.widget)
    pt = PateThread(f, pate_widget)
    pate_widget.pate_thread = pt
    pt.start()


def quitCleanup():
    PateMcad.stopAllServers()


def register():

    Settings().register_group("pate", "PATE")

    Settings().register_setting("pate.mcadDockerName", """
    {
        "title" : "MCAD Docker image name",
        "type" : "string",
        "default" : null,
        "description" : "If this is set, PATE will run the MCAD docker image to analyze instruction timing."
    }
    """)
    #print("pate.mcadDockerName:", Settings().get_string("pate.mcadDockerName"))

    UIAction.registerAction('Pate...')
    UIActionHandler.globalActions().bindAction('Pate...', UIAction(launch_pate))
    Menu.mainMenu('Plugins').addAction('Pate...', 'Pate', True)

    QCoreApplication.instance().aboutToQuit.connect(quitCleanup)


register()
