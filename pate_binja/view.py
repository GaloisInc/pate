# Copyright 2023-2024, Galois Inc. All rights reserved.

from __future__ import annotations

import io
import os.path
import signal
import time
from subprocess import Popen, TimeoutExpired
from threading import Thread, Condition
from typing import Optional

from binaryninja import execute_on_main_thread_and_wait, BinaryView, interaction, \
    load
from binaryninja.enums import BranchType, HighlightStandardColor, ThemeColor
from binaryninja.flowgraph import FlowGraph, FlowGraphNode, FlowGraphEdge, EdgeStyle
from binaryninjaui import UIAction, UIActionHandler, Menu, UIActionContext, \
    FlowGraphWidget, FileContext

# PySide6 import MUST be after import of binaryninjaui
from PySide6.QtCore import Qt
from PySide6.QtGui import QMouseEvent
from PySide6.QtWidgets import QHBoxLayout, QLabel, QVBoxLayout, QLineEdit, QPlainTextEdit, QDialog, QWidget, \
    QDialogButtonBox, QSplitter

from . import pate


class PateWidget(QWidget):
    def __init__(self, context: UIActionContext, parent: QWidget, filename: str, config: dict) -> None:
        super().__init__(parent)
        self.context = context

        self.filename = filename
        self.config = config
        self.pate_thread: PateThread = None

        self.flow_graph_widget = MyFlowGraphWidget(self)

        self.output_field = QPlainTextEdit()
        self.output_field.setReadOnly(True)
        self.output_field.setMaximumBlockCount(1000000)

        self.cmd_field = QLineEdit()
        self.cmd_field.setEnabled(False)
        self.cmd_field.returnPressed.connect(self.onPateCommandReturnPressed)

        cmd_field_layout = QHBoxLayout()
        cmd_field_layout.addWidget(QLabel("Pate Command: "))
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

        #self.loadBinaryViews()
        #self.hackaroo()

    def loadBinaryViews(self):
        # TODO: May need a progress feedback. Can this take a significant amount of time?
        config = self.config
        if config:
            cwd = config.get('cwd')
            original = config.get('original')
            patched = config.get('patched')
            if cwd and original:
                #self.oBv = load(os.path.join(cwd, original))
                #self.oBv.add_analysis_completion_event(lambda: print('finished loading', original))
                #self.oBv = oF.getRawData()
                oF = FileContext.openFilename(os.path.join(cwd, original))
                if oF:
                    vF = self.context.openFileContext(oF)
            if cwd and patched:
                self.pBv = load(os.path.join(cwd, patched))
                self.pBv.add_analysis_completion_event(lambda: print('finished loading', patched))

    def hackaroo(self):
        a = 0x400c
        bb = self.oBv.get_basic_blocks_at(a)
        print(bb)

    def closeEvent(self, event):
        if self.pate_thread:
            self.pate_thread.cancel()

    def hideEvent(self, event):
        if self.pate_thread:
            self.pate_thread.cancel()

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
        if not replay:
            self.cmd_field.setText('')
            self.cmd_field.setEnabled(True)


class GuiUserInteraction(pate.PateUserInteraction):
    def __init__(self, pate_widget: PateWidget, replay: bool = False,
                 show_ce_trace: bool = False):
        self.pate_widget = pate_widget
        self.replay = replay
        self.show_ce_trace = show_ce_trace

    def ask_user(self, prompt: str, choices: list[str]) -> Optional[str]:
        execute_on_main_thread_and_wait(lambda: self.pate_widget.ask_user(prompt, choices, self.replay))
        if self.replay:
            execute_on_main_thread_and_wait(lambda: self.pate_widget.output_field.appendPlainText('Pate Command: auto replay\n'))
            return '42'  # Return anything (its ignored) for fast replay
        # Wait for user to respond to prompt. This happens on the GUI thread.
        urc = self.pate_widget.user_response_condition
        with urc:
            while self.pate_widget.user_response is None:
                urc.wait()
            choice = self.pate_widget.user_response
            self.pate_widget.user_response = None
        execute_on_main_thread_and_wait(lambda: self.pate_widget.output_field.appendPlainText(f'Pate Command: {choice}\n'))
        return choice

    def show_message(self, msg: str) -> None:
        execute_on_main_thread_and_wait(lambda: self.pate_widget.output_field.appendPlainText(msg))

    def show_cfar_graph(self, graph: pate.CFARGraph) -> None:
        execute_on_main_thread_and_wait(lambda: self.pate_widget.flow_graph_widget.build_pate_flow_graph(graph, self.show_ce_trace))

        promptNode = graph.getPromptNode()
        if promptNode:
            # Experiment focusing graph display on a particular node. Only work with sleep. Probably need to do this
            # on some event that is called when graph is rendered.
            time.sleep(1)
            execute_on_main_thread_and_wait(lambda: self.pate_widget.flow_graph_widget.showCfar(promptNode))


class PateThread(Thread):
    proc: Popen or None
    oBv: BinaryView | None
    pBv: BinaryView | None

    # TODO: Look at interaction.run_progress_dialog
    # handle cancel and restart
    def __init__(self, bv, run_fn, pate_widget: PateWidget, replay=False, show_ce_trace=True, trace_file=None):
        super().__init__(name="Pate " + pate_widget.filename)
        self.daemon = True
        self.pate_widget = pate_widget
        self.replay = replay
        self.run_fn = run_fn
        self.trace_file = trace_file
        self.show_ce_trace = show_ce_trace
        self.proc = None
        self.oBv = None
        self.pBv = None

    def run(self):
        x = self.run_fn(self.replay)
        if self.trace_file:
            with open(self.trace_file, "w") as trace:
                with x as proc:
                    self.proc = proc
                    self._command_loop(proc, self.show_ce_trace, trace)
        else:
            with x as proc:
                self.proc = proc
                self._command_loop(proc, self.show_ce_trace)

    def cancel(self) -> None:
        if self.proc and self.is_alive():
            # Closing input should cause PATE process to exit
            self.proc.stdin.close()
            try:
                self.proc.wait(3)
            except TimeoutExpired:
                # Orderly shutdown did not work, kill the process group
                print('KILLING PATE Process')
                self.proc.killpg(self.proc.pid, signal.SIGKILL)

    def _command_loop(self, proc: Popen, show_ce_trace: bool = False, trace_io=None):

        #self.progress = 'Pate running...'
        execute_on_main_thread_and_wait(lambda: self.pate_widget.cmd_field.setText('Pate running...'))

        user = GuiUserInteraction(self.pate_widget, self.replay, show_ce_trace)
        pate_wrapper = pate.PateWrapper(user, proc.stdout, proc.stdin, trace_io)

        pate_wrapper.command_loop()

        execute_on_main_thread_and_wait(lambda: self.pate_widget.cmd_field.setText('Pate finished'))


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


class PateCfarExitDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)

        self.setWindowTitle("CFAR Exit Info")

        self.commonField = QPlainTextEdit()
        self.commonField.setReadOnly(True)
        self.commonField.setMaximumBlockCount(1000)

        self.originalField = QPlainTextEdit()
        self.originalField.setReadOnly(True)
        self.originalField.setMaximumBlockCount(1000)

        self.patchedField = QPlainTextEdit()
        self.patchedField.setReadOnly(True)
        self.patchedField.setMaximumBlockCount(1000)

        hsplitter = QSplitter()
        hsplitter.setOrientation(Qt.Orientation.Horizontal)
        hsplitter.addWidget(self.originalField)
        hsplitter.addWidget(self.patchedField)

        vsplitter = QSplitter()
        vsplitter.setOrientation(Qt.Orientation.Vertical)
        vsplitter.addWidget(self.commonField)
        vsplitter.addWidget(hsplitter)

        QBtn = QDialogButtonBox.Ok
        self.buttonBox = QDialogButtonBox(QBtn)
        self.buttonBox.accepted.connect(self.accept)

        main_layout = QHBoxLayout()
        main_layout.addWidget(vsplitter)
        #main_layout.addWidget(self.buttonBox)
        self.setLayout(main_layout)


class MyFlowGraphWidget(FlowGraphWidget):

    flowGraph: FlowGraph
    cfarGraph: pate.CFARGraph
    flowToCfar: dict[FlowGraphNode, pate.CFARNode]
    cfarToFlow: dict[pate.CFARNode, FlowGraphNode]
    def __init__(self, parent: QWidget, view: BinaryView=None, graph: FlowGraph=None):
        super().__init__(parent, view, graph)
        self.flowToCfar = {}

    def build_pate_flow_graph(self,
                              cfarGraph: pate.CFARGraph,
                              show_ce_trace: bool = False):
        self.flowGraph = FlowGraph()
        self.cfarGraph = cfarGraph

        # First create all nodes
        self.cfarToFlow = {}
        cfar_node: pate.CFARNode
        for cfar_node in self.cfarGraph.nodes.values():
            flow_node = FlowGraphNode(self.flowGraph)

            self.flowToCfar[flow_node] = cfar_node

            out = io.StringIO()

            out.write(cfar_node.id.replace(' <- ', '\n  <- '))
            out.write('\n')

            cfar_node.pprint_node_contents('', out, False)  # show_ce_trace) Disable trace in node

            flow_node.lines = out.getvalue().split('\n')
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
                    edgeStyle = EdgeStyle(width=3, theme_color=ThemeColor.GraphNodeOutlineColor)
                else:
                    edgeStyle = EdgeStyle(width=1, theme_color=ThemeColor.GraphNodeOutlineColor)
                flow_node.add_outgoing_edge(BranchType.UserDefinedBranch, flow_exit, edgeStyle)

        self.setGraph(self.flowGraph)

    def showCfar(self, focusCfar: pate.CFARNode):
        focusFlow: FlowGraphNode | None = self.cfarToFlow.get(focusCfar.id)
        #print('focusCfar.id', focusCfar.id)
        #print('focusFlowNode', focusFlow)
        if focusFlow:
            focusFlow.highlight = HighlightStandardColor.BlueHighlightColor
            self.showNode(focusFlow)

    def mousePressEvent(self, event: QMouseEvent):
        node = self.getNodeForMouseEvent(event)
        edgeTuple = self.getEdgeForMouseEvent(event)
        # if node:
        #     print("Node: ", self.flowToCfarNode[node].id)
        # if edgeTuple:
        #     print("Edge source: ", self.flowToCfarNode[edgeTuple[0].source].id)
        #     print("Edge target: ", self.flowToCfarNode[edgeTuple[0].target].id)
        #     print("Edge incoming: ", edgeTuple[1])

        if edgeTuple:
            self.showEdgeExitInfo(edgeTuple)

    def showEdgeExitInfo(self, edgeTuple: tuple[FlowGraphEdge, bool]) -> None:
        edge = edgeTuple[0]
        incoming = edgeTuple[1]  # Direction of edge depends on which half was clicked
        if incoming:
            sourceCfarNode = self.flowToCfar[edge.target]
            exitCfarNode = self.flowToCfar[edge.source]
        else:
            sourceCfarNode = self.flowToCfar[edge.source]
            exitCfarNode = self.flowToCfar[edge.target]
        self.showCfarExitInfo(sourceCfarNode, exitCfarNode)

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
                self.showExitTraceInfo(sourceCfarNode, trace, 'Trace')
            return True
        else:
            # TODO: dialog?
            return False

    def showExitTraceInfo(self, sourceCfarNode: pate.CFARNode, trace: dict, label: str):
        d = PateCfarExitDialog(parent=self)
        with io.StringIO() as out:
            sourceCfarNode.pprint_node_event_trace_domain(trace, label, out=out)
            d.commonField.setPlainText(out.getvalue())
        with io.StringIO() as out:
            sourceCfarNode.pprint_node_event_trace_original(trace, label, out=out)
            d.originalField.setPlainText(out.getvalue())
        with io.StringIO() as out:
            sourceCfarNode.pprint_node_event_trace_patched(trace, label, out=out)
            d.patchedField.setPlainText(out.getvalue())
        d.exec()


def launch_pate(context: UIActionContext):

    f = interaction.get_open_filename_input(
        "Run PATE",
        "PATE Run Configuration (*.run-config.json);;PATE Replay (*.replay)")

    if f is None:
        return

    if f.endswith(".run-config.json"):
        replay = False
        trace_file = os.path.join(os.path.dirname(f), 'lastrun.replay')
        config = pate.get_run_config(f)
    elif f.endswith(".replay"):
        replay = True
        trace_file = None
        config = {}  # TODO: need config for replay. Save it in replay file as first line?

    pate_widget = PateWidget(context.context, context.widget, f, config)
    tab = context.context.createTabForWidget("PATE " + os.path.basename(f), pate_widget)

    if replay:
        pt = PateThread(None, lambda i: pate.run_replay(f), pate_widget, replay=replay, trace_file=trace_file)
    else:
        pt = PateThread(None, lambda i: pate.run_config(config), pate_widget, replay=replay, trace_file=trace_file)

    pate_widget.pate_thread = pt
    pt.start()


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


register()
