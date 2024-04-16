# Copyright 2023-2024, Galois Inc. All rights reserved.

from __future__ import annotations

import io
import os.path
import re
import time
from difflib import HtmlDiff
from threading import Thread, Condition
from typing import Optional

from binaryninja import execute_on_main_thread_and_wait, BinaryView, interaction, \
    load, DisassemblyTextLine, Architecture
from binaryninja.enums import BranchType, HighlightStandardColor, ThemeColor
from binaryninja import InstructionTextToken as ITT
from binaryninja.enums import InstructionTextTokenType as ITTType
from binaryninja.flowgraph import FlowGraph, FlowGraphNode, FlowGraphEdge, EdgeStyle
from binaryninjaui import UIAction, UIActionHandler, Menu, UIActionContext, \
    FlowGraphWidget, FileContext, UIContext, ViewFrame, ViewLocation

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

    def loadBinaryViews(self, config: dict):
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

        with load(self.originalFilename) as obv:
            original_lines = list(map(lambda line: subDisassemblyForInstAddr(line, obv), original_lines))
        with load(self.patchedFilename) as pbv:
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
            instBytes = bv.read(offset, instLen)
            instructions.append(instBytes)

        if instructions:
            # Get the cycle counts from MCAD
            # TODO: Check for gRPC error
            cycleCounts = mcadServer.request_cycle_counts(instructions)

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
            lambda: self.pate_widget.loadBinaryViews(config))
        execute_on_main_thread_and_wait(
            lambda: self.pate_widget.context.createTabForWidget("PATE " + os.path.basename(self.filename),
                                                                self.pate_widget))

        # Hack to pre-start MCAD server(s)
        with load(self.pate_widget.originalFilename) as bv:
            arch = bv.arch
            PateMcad.getServerForArch(arch.name)
            if arch.name == 'thumb2':
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

        # Add Labels?
        # traceDiffBox = QVBoxLayout()
        # traceDiffBox.addWidget(QLabel("Trace"))
        # traceDiffBox.addWidget(self.traceDiffField)
        #
        # traceDiffWidget = QWidget()
        # traceDiffWidget.setLayout(traceDiffBox)

        vsplitter = QSplitter()
        vsplitter.setOrientation(Qt.Orientation.Vertical)
        vsplitter.addWidget(self.domainField)
        vsplitter.addWidget(self.traceDiffField)

        main_layout = QHBoxLayout()
        main_layout.addWidget(vsplitter)
        self.setLayout(main_layout)

    def setTrace(self, trace: dict, label: str):
        with io.StringIO() as out:
            pate.pprint_node_event_trace_domain(trace, out=out)
            self.domainField.setPlainText(out.getvalue())

        # collect trace text content, for formatting below
        original_lines = []
        patched_lines = []
        with io.StringIO() as out:
            pate.pprint_node_event_trace_original(trace, out=out)
            original_lines = out.getvalue().splitlines()
        with io.StringIO() as out:
            pate.pprint_node_event_trace_patched(trace, out=out)
            patched_lines = out.getvalue().splitlines()

        # Replace addr lines with binja disassembly
        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)
        if pw:
            original_lines, patched_lines = pw.injectBinjaDissembly(original_lines, patched_lines)

        htmlDiff = HtmlDiff()
        html = htmlDiff.make_file(original_lines, patched_lines,
                                  fromdesc=f'{label} (original)', todesc=f'{label} (patched)')
        self.traceDiffField.setHtml(html)


class PateCfarExitDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.resize(1100, 600)
        self.setWindowTitle("CFAR Exit Info")

        self.traceWidget = TraceWidget(self)

        main_layout = QHBoxLayout()
        main_layout.addWidget(self.traceWidget)
        self.setLayout(main_layout)

    def setTrace(self, trace: dict, label: str):
        self.traceWidget.setTrace(trace, label)


class PateCfarEqCondDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.resize(1500, 800)

        self.setWindowTitle("CFAR Equivalence Condition")

        self.commonField = QPlainTextEdit()
        self.commonField.setReadOnly(True)
        self.commonField.setMaximumBlockCount(1000)

        self.trueTraceWidget = TraceWidget(self)
        self.falseTraceWidget = TraceWidget(self)

        trueFalseSplitter = QSplitter()
        trueFalseSplitter.setOrientation(Qt.Orientation.Horizontal)
        trueFalseSplitter.addWidget(self.trueTraceWidget)
        trueFalseSplitter.addWidget(self.falseTraceWidget)

        predSplitter = QSplitter()
        predSplitter.setOrientation(Qt.Orientation.Vertical)
        predSplitter.addWidget(self.commonField)
        predSplitter.addWidget(trueFalseSplitter)

        main_layout = QHBoxLayout()
        main_layout.addWidget(predSplitter)
        self.setLayout(main_layout)

    def setTrueTrace(self, trace: dict, label: str):
        self.trueTraceWidget.setTrace(trace, label)

    def setFalseTrace(self, trace: dict, label: str):
        self.falseTraceWidget.setTrace(trace, label)


class InstTreeDiffWidget(QWidget):
    def __init__(self, parent):
        super().__init__(parent)

        self.instDiffField = QTextEdit()
        self.instDiffField.setReadOnly(True)

        main_layout = QHBoxLayout()
        main_layout.addWidget(self.instDiffField)
        self.setLayout(main_layout)

    def setInstTrees(self, instTrees: dict, label: str):
        if not instTrees:
            self.instDiffField.append("No Instruction Trees")
            return

        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)

        original_lines = []
        if instTrees.get('original'):
            originalInstTree = instTrees['original']
            with load(pw.originalFilename) as obv:
                pw.mcad_annotate_inst_tree(originalInstTree, obv)
                original_lines = self.getInstTreeLines(originalInstTree, obv)

        patched_lines = []
        if instTrees.get('patched'):
            patchedInstTree = instTrees['patched']
            with load(pw.patchedFilename) as pbv:
                pw.mcad_annotate_inst_tree(patchedInstTree, pbv)
                patched_lines = self.getInstTreeLines(patchedInstTree, pbv)

        htmlDiff = HtmlDiff()
        html = htmlDiff.make_file(original_lines, patched_lines,
                                  fromdesc=f'{label} (original)', todesc=f'{label} (patched)')
        self.instDiffField.setHtml(html)

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
    def __init__(self, parent=None):
        super().__init__(parent)
        self.resize(1100, 600)
        self.setWindowTitle("CFAR Inst Trees")

        pw: Optional[PateWidget] = getAncestorInstanceOf(self, PateWidget)

        # TODO: Should we only load the obv once per pate widget?
        obv = load(pw.originalFilename)
        self.originalInstTreeGraphWidget = InstTreeGraphWidget(self, obv)

        # TODO: Should we only load the pbv once per pate widget?
        pbv = load(pw.patchedFilename)
        self.patchedInstTreeGraphWidget = InstTreeGraphWidget(self, pbv)

        hsplitter = QSplitter()
        hsplitter.setOrientation(Qt.Orientation.Horizontal)
        hsplitter.addWidget(self.originalInstTreeGraphWidget)
        hsplitter.addWidget(self.patchedInstTreeGraphWidget)

        self.instTreeDiffWidget = InstTreeDiffWidget(self)

        vsplitter = QSplitter()
        vsplitter.setOrientation(Qt.Orientation.Vertical)
        vsplitter.addWidget(hsplitter)
        vsplitter.addWidget(self.instTreeDiffWidget)

        main_layout = QHBoxLayout()
        main_layout.addWidget(vsplitter)
        self.setLayout(main_layout)

    def setInstTrees(self, instTrees: dict, label: str):
        if instTrees.get('original'):
            self.originalInstTreeGraphWidget.setInstTree(instTrees['original'])
        if instTrees.get('patched'):
            self.patchedInstTreeGraphWidget.setInstTree(instTrees['patched'])
        self.instTreeDiffWidget.setInstTrees(instTrees, label)


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
                action = QAction('Show Inst Trees', self)
                action.triggered.connect(lambda _: self.showInstTreeInfo(cfarNode.instruction_trees,
                                                                         cfarNode.id))
                menu.addAction(action)

            if menu.actions():
                menu.exec_(event.globalPos())

    def showCfarEqCondDialog(self, cfarNode: pate.CFARNode):
        d = PateCfarEqCondDialog(parent=self)
        d.commonField.appendPlainText(f'CFAR ID: {cfarNode.id}')
        with io.StringIO() as out:
            pate.pprint_symbolic(out, cfarNode.predicate)
            d.commonField.appendPlainText(out.getvalue())
        d.setTrueTrace(cfarNode.trace_true, 'True Trace')
        d.setFalseTrace(cfarNode.trace_true, 'False Trace')
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
                action = QAction(f'Show CFAR Exit Info', self)
                action.triggered.connect(lambda _: self.showCfarExitInfo(sourceCfarNode, exitCfarNode))
                menu.addAction(action)

            if exitMetaData.get('instruction_trees_to_exit'):
                action = QAction(f'Show Inst Trees to Exit', self)
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
                self.showExitTraceInfo(sourceCfarNode, ceTrace, 'Counter-Example Trace')
            return True
        elif trace:
            if not simulate:
                self.showExitTraceInfo(sourceCfarNode, trace, 'Witness Trace')
            return True
        else:
            # TODO: dialog?
            return False

    def showExitTraceInfo(self, sourceCfarNode: pate.CFARNode, trace: dict, label: str):
        d = PateCfarExitDialog(self)
        d.setTrace(trace, label)
        d.exec()

    def showInstTreeInfo(self, instTrees: dict, label: str):
        d = PateCfarInstTreeDialog(self)
        d.setWindowTitle(d.windowTitle() + ' ' + label)
        d.setInstTrees(instTrees, '')
        d.show()


def getInstArch(addr: int, bv: BinaryView) -> Architecture:
    # The following should work, but bv.get_functions_containing always returns [].
    # flist = bv.get_functions_containing(addr)
    # if flist:
    #     arch = flist[0].arch
    # else:
    #     arch = bv.arch
    # return arch

    # TODO: This is a hack. Could not find a better way to do this.
    fs = bv.get_previous_function_start_before(addr + 1) # Need +1 or it finds prev function
    #print("FS:", f'{fs:08x}')
    f = bv.get_recent_function_at(fs)  # recent?
    #print("F:", f)
    farch = f.arch
    #print("F-arch", farch)
    return farch


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

def getTabForFilename(context: UIContext, filename: str, loadIfDoesNotExist: bool = True) -> QWidget | None:
    """Find Tab for filename."""
    tab = None
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
    #print('Found Tab:', tab, "for filename:", filename)
    return tab


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
    pt.start()  # This will call pate_widget.loadBinaryViews() once config is loaded

# class PateConfigDialog(QDialog):
#     def __init__(self, context: UIActionContext, parent=None):
#         super().__init__(parent)
#
#         self.setWindowTitle("Pate Run Configuration")
#
#         orig_layout = QHBoxLayout()
#         orig_layout.addWidget(QLabel("Original Binary"))
#         self.orig_text = QLineEdit()
#         orig_layout.addWidget(self.orig_text)
#         orig_button = QPushButton("...")
#         orig_layout.addWidget(orig_button)
#
#         patch_layout = QHBoxLayout()
#         patch_layout.addWidget(QLabel("Patched Binary"))
#         self.patch_text = QLineEdit()
#         patch_layout.addWidget(self.patch_text)
#         patch_button = QPushButton("...")
#         patch_layout.addWidget(patch_button)
#
#         QBtn = QDialogButtonBox.Ok | QDialogButtonBox.Cancel
#         self.buttonBox = QDialogButtonBox(QBtn)
#         self.buttonBox.accepted.connect(self.accept)
#
#         self.layout = QVBoxLayout()
#         message = QLabel("Something happened, is that OK?")
#         self.layout.addLayout(orig_layout)
#         self.layout.addLayout(patch_layout)
#         self.layout.addWidget(self.buttonBox)
#         self.setLayout(self.layout)


# def launch_pate_experiment(context: UIActionContext):
#     # Prompt for existing config or new
#     # TODO:
#     msgBox = QMessageBox()
#     msgBox.setText('Pate Run Configuration')
#     msgBox.setInformativeText('Open an existing PATE run configuration file or create a new one.')
#     openButton = msgBox.addButton('Open...', QMessageBox.ActionRole)
#     newButton = msgBox.addButton('New...', QMessageBox.ActionRole)
#     cancelButton = msgBox.addButton(QMessageBox.Cancel)
#     msgBox.setDefaultButton(openButton)
#     msgBox.exec()
#
#     if openButton.clicked():
#         print('open')
#     elif newButton.clicked():
#         print('new')
#     elif cancelButton.clicked():
#         print('cancel')
#
#     return
#
#     # Existing
#     # - Open file dialog
#     # - Show config dialog
#     #   - allows config to be edited
#     #   - buttons:
#     #      - cancel - abort launch, close dialog
#     #      - update - update config file, dialog remains open, bonus, only active if changes
#     #      - run - run the configuration, save if changes (prompt?)
#     #
#     # New
#     # - Save file dialog
#     # - Show config dialog (empty config)
#     #    - same behaviour as above, ut starts empty
#
#     fields = []
#     fields.append(OpenFileNameField("Original"))
#     fields.append(OpenFileNameField("Binary"))
#     fields.append(MultilineTextField("Args"))
#     fnort = interaction.get_form_input(fields, "Enter Pate Parameters")
#     print(list(map(lambda x: x.result, fields)))
#
#     dlg = PateConfigDialog(context.widget)
#     if dlg.exec():
#         print("Success!")
#     else:
#         print("Cancel!")


# pate_window = None
#
#
# def launch_pate_old(context: UIActionContext):
#     global pate_window
#     if not pate_window:
#         pate_window = PateWindow(context, parent=context.widget)
#     pate_window.show()
#     # Make sure window is not minimized
#     pate_window.setWindowState(pate_window.windowState() & ~Qt.WindowMinimized | Qt.WindowActive)
#     pate_window.raise_()

def quitCleanup():
    PateMcad.stopAllServers()

def register():
    #PluginCommand.register('Run Pate ch10', 'Run Pate Verifier and show flow graph', run_pate_thread_may23_ch10)
    #PluginCommand.register('Run Pate t1', 'Run Pate Verifier and show flow graph', run_pate_thread_nov23_t1_room1018)
    #PluginCommand.register('Run Pate t4', 'Run Pate Verifier and show flow graph', run_pate_thread_nov23_t4_dendy1011)

    # [JCC 20240216] If we want to use setting rather than env vars...
    # Settings().register_group("pate", "PATE")
    # Settings().register_setting("pate.source", """
    # 	{
    # 		"title" : "PATE Verifier Source Directory",
    # 		"type" : "string",
    # 		"default" : null,
    # 		"description" : "If this is set, PATE will run as built in the source directory rather than using the docker image."
    # 	}
    # 	""")
    #
    # print("pate.source:", Settings().get_string("pate.source"))
    # print("contains(pate.source):", Settings().contains("pate.source"))

    UIAction.registerAction('Pate...')
    UIActionHandler.globalActions().bindAction('Pate...', UIAction(launch_pate))
    Menu.mainMenu('Plugins').addAction('Pate...', 'Pate', True)

    QCoreApplication.instance().aboutToQuit.connect(quitCleanup)


register()
