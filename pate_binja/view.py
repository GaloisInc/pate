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
    load, execute_on_main_thread
from binaryninja.enums import BranchType, HighlightStandardColor, ThemeColor
from binaryninja.flowgraph import FlowGraph, FlowGraphNode, FlowGraphEdge, EdgeStyle
from binaryninjaui import UIAction, UIActionHandler, Menu, UIActionContext, \
    FlowGraphWidget, FileContext, UIContext, ViewFrame, ViewLocation

# PySide6 import MUST be after import of binaryninjaui
from PySide6.QtCore import Qt
from PySide6.QtGui import QMouseEvent, QAction, QContextMenuEvent
from PySide6.QtWidgets import QHBoxLayout, QLabel, QVBoxLayout, QLineEdit, QPlainTextEdit, QDialog, QWidget, \
    QDialogButtonBox, QSplitter, QMenu

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
        self.cmd_field.setText('')
        self.cmd_field.setEnabled(True)
        self.cmd_field.setFocus()


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
        if promptNode:
            self.pate_widget.flow_graph_widget.flowGraph.layout_and_wait()
            execute_on_main_thread_and_wait(lambda: self.pate_widget.flow_graph_widget.showCfar(promptNode))


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

    pate_widget: PateWidget
    flowGraph: FlowGraph
    cfarGraph: pate.CFARGraph
    flowToCfar: dict[FlowGraphNode, pate.CFARNode]
    cfarToFlow: dict[pate.CFARNode, FlowGraphNode]

    def __init__(self, parent: QWidget, pate_widget: PateWidget, view: BinaryView=None, graph: FlowGraph=None):
        super().__init__(parent, view, graph)
        self.pate_widget = pate_widget

        #self.setContextMenuPolicy(Qt.CustomContextMenu)
        #self.customContextMenuRequested.connect(self.customContextMenu)

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

        if node:
            self.gotoAddressPopupMenu(event, node)

        elif edgeTuple:
            self.showEdgeExitInfo(edgeTuple)

    def gotoAddressPopupMenu(self, event: QMouseEvent, node: FlowGraphNode):
        cfarNode = self.flowToCfar[node]
        if cfarNode and (cfarNode.original_addr or cfarNode.patched_addr):
            context = QMenu(self)
            gotoOriginalAction = None
            gotoPatchedAction = None
            if cfarNode.original_addr:
                gotoOriginalAction = QAction(f'Goto original address {hex(cfarNode.original_addr)}', self)
                context.addAction(gotoOriginalAction)
            if cfarNode.patched_addr:
                gotoPatchedAction = QAction(f'Goto patched address {hex(cfarNode.patched_addr)}', self)
                context.addAction(gotoPatchedAction)
            choice = context.exec(event.globalPos())
            #print('context choice:', choice)
            if choice == gotoOriginalAction:
                self.pate_widget.gotoOriginalAddress(cfarNode.original_addr)
            elif choice == gotoPatchedAction:
                self.pate_widget.gotoPatchedAddress(cfarNode.patched_addr)

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
            pate.pprint_node_event_trace_domain(trace, label, out=out)
            d.commonField.setPlainText(out.getvalue())
        with io.StringIO() as out:
            pate.pprint_node_event_trace_original(trace, label, out=out)
            d.originalField.setPlainText(out.getvalue())
        with io.StringIO() as out:
            pate.pprint_node_event_trace_patched(trace, label, out=out)
            d.patchedField.setPlainText(out.getvalue())
        d.exec()


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
