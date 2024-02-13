# Copyright (c) 2023 Galois Inc

from __future__ import annotations

import io
import os.path
import threading
from subprocess import Popen
from typing import Optional

from binaryninja import show_graph_report, execute_on_main_thread_and_wait, BinaryView, OpenFileNameField, interaction, \
    MultilineTextField
from binaryninja.enums import BranchType, HighlightStandardColor
from binaryninja.flowgraph import FlowGraph, FlowGraphNode
from binaryninja.plugin import BackgroundTaskThread
from binaryninjaui import GlobalAreaWidget, GlobalArea, UIAction, UIActionHandler, Menu, UIActionContext, \
    FlowGraphWidget

# PySide6 import MUST be after import of binaryninjaui
from PySide6.QtCore import Qt
from PySide6.QtGui import QMouseEvent
from PySide6.QtWidgets import QHBoxLayout, QLabel, QVBoxLayout, QLineEdit, QPlainTextEdit, QDialog, QWidget, \
    QDialogButtonBox, QPushButton, QMessageBox

from . import pate

instance_id = 0

# TODO: find a way to do this without a global variable
pateWidget: PateWidget


class PateWidget(GlobalAreaWidget):
    def __init__(self, name):
        global instance_id
        global pateWidget
        GlobalAreaWidget.__init__(self, name)
        pateWidget = self

        self.outputfield = QPlainTextEdit()
        self.outputfield.setReadOnly(True)
        self.outputfield.setMaximumBlockCount(1000000)

        textfield_layout = QHBoxLayout()
        textfield_layout.addWidget(QLabel("Pate Command: "))
        self.textfield = QLineEdit()
        self.textfield.setEnabled(False)
        textfield_layout.addWidget(self.textfield)
        textfield_layout.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.textfield.returnPressed.connect(self.onPateCommandReturnPressed)

        layout = QVBoxLayout()
        layout.addWidget(self.outputfield)
        layout.addLayout(textfield_layout)
        self.setLayout(layout)

        instance_id += 1
        self.data = None

        self.user_response_condition = threading.Condition()
        self.user_response = None

    def onPateCommandReturnPressed(self):
        user_response = self.textfield.text()
        # TODO: validate here or use QLineEdit validation mechanism
        self.textfield.setText('Pate running...')
        self.textfield.setEnabled(False)
        # Notify Pate background thread
        with self.user_response_condition:
            self.user_response = user_response
            self.user_response_condition.notify()

    def ask_user(self, prompt: str, choices: list[str], replay: bool):
        query = '\n' + prompt + '\n'
        for i, e in enumerate(choices):
            query += '  {}\n'.format(e)
        self.outputfield.appendPlainText(query)
        if not replay:
            self.textfield.setText('')
            self.textfield.setEnabled(True)


class GuiUserInteraction(pate.PateUserInteraction):
    def __init__(self, pateWidget: PateWidget, replay: bool = False,
                 show_ce_trace: bool = False):
        self.pateWidget = pateWidget
        self.replay = replay
        self.show_ce_trace = show_ce_trace

    def ask_user(self, prompt: str, choices: list[str]) -> Optional[str]:
        execute_on_main_thread_and_wait(lambda: self.pateWidget.ask_user(prompt, choices, self.replay))
        if self.replay:
            execute_on_main_thread_and_wait(lambda: self.pateWidget.outputfield.appendPlainText('Pate Command: auto replay\n'))
            return '42' # Return anything (its ignored) for fast replay
        # Wait for user to respond to prompt. This happens on the GUI thread.
        urc = self.pateWidget.user_response_condition
        with urc:
            while self.pateWidget.user_response is None:
                urc.wait()
            choice = self.pateWidget.user_response
            self.pateWidget.user_response = None
            execute_on_main_thread_and_wait(self.pateWidget.outputfield.appendPlainText(f'Pate Command: {choice}\n'))
            return choice

    def show_message(self, msg) -> None:
        execute_on_main_thread_and_wait(lambda: self.pateWidget.outputfield.appendPlainText(msg))

    def show_cfar_graph(self, graph: pate.CFARGraph) -> None:
        flow_graph = build_pate_flow_graph(graph, self.show_ce_trace)
        execute_on_main_thread_and_wait(lambda: show_graph_report("Pate Flowgraph", flow_graph))


class PateThread(BackgroundTaskThread):
    # TODO: Look at interaction.run_progress_dialog
    # handle cancel and restart
    def __init__(self, bv, run_fn, replay=False, show_ce_trace=True, trace_file=None):
        BackgroundTaskThread.__init__(self, "Pate Process", True)
        self.replay = replay
        self.run_fn = run_fn
        self.trace_file = trace_file
        self.show_ce_trace = show_ce_trace

    def run(self):
        # # TODO: OK to do this on the background thread?
        # ans = show_message_box(
        #     "Pate msg box", "Run pate in replay mode?",
        #     MessageBoxButtonSet.YesNoCancelButtonSet, MessageBoxIcon.QuestionIcon
        # )
        #
        # match ans:
        #     case MessageBoxButtonResult.YesButton:
        #         # Replay mode
        #         self.replay = True
        #     case MessageBoxButtonResult.NoButton:
        #         # Live mode
        #         self.replay = False
        #     case _:
        #         return

        x = self.run_fn(self.replay)
        if self.trace_file:
            with open(self.trace_file, "w") as trace:
                with x as proc:
                    self._command_loop(proc, self.show_ce_trace, trace)
        else:
            with x as proc:
                self._command_loop(proc, self.show_ce_trace)

    def _command_loop(self, proc: Popen, show_ce_trace: bool = False, trace_io=None):
        global pateWidget

        #self.progress = 'Pate running...'
        execute_on_main_thread_and_wait(lambda: pateWidget.textfield.setText('Pate running...'))

        user = GuiUserInteraction(pateWidget, self.replay, show_ce_trace)
        pate_wrapper = pate.PateWrapper(user, proc.stdout, proc.stdin, trace_io)

        pate_wrapper.command_loop()

        #self.progress = 'Pate finished.'
        execute_on_main_thread_and_wait(lambda: pateWidget.textfield.setText('Pate finished.'))


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


def build_pate_flow_graph(cfar_graph: pate.CFARGraph,
                          show_ce_trace: bool = False):
    flow_graph = FlowGraph()

    # First create all nodes
    flow_nodes = {}
    cfar_node: pate.CFARNode
    for cfar_node in cfar_graph.nodes.values():
        flow_node = FlowGraphNode(flow_graph)

        out = io.StringIO()

        out.write(cfar_node.id.replace(' <- ','\n  <- '))
        out.write('\n')

        cfar_node.pprint_node_contents('', out, show_ce_trace)

        flow_node.lines = out.getvalue().split('\n')
        #flow_node.lines = [lines[0]]

        if cfar_node.id.find(' vs ') >= 0:
            # Per discussion wit dan, it does not make sense to highlight these.
            # flow_node.highlight = HighlightStandardColor.BlueHighlightColor
            pass
        elif cfar_node.id.find('(original') >= 0:
            flow_node.highlight = HighlightStandardColor.GreenHighlightColor
        elif cfar_node.id.find('(patched)') >= 0:
            flow_node.highlight = HighlightStandardColor.MagentaHighlightColor

        flow_graph.append(flow_node)
        flow_nodes[cfar_node.id] = flow_node

    # Add edges
    cfar_node: pate.CFARNode
    for cfar_node in cfar_graph.nodes.values():
        flow_node = flow_nodes[cfar_node.id]
        cfar_exit: pate.CFARNode
        for cfar_exit in cfar_node.exits:
            flow_exit = flow_nodes[cfar_exit.id]
            flow_node.add_outgoing_edge(BranchType.UnconditionalBranch, flow_exit)

    return flow_graph


class MyFlowGraphWidget(FlowGraphWidget):
    def __init__(self, parent: QWidget, view: BinaryView=None, graph: FlowGraph=None):
        super().__init__(parent, view, graph)

    def mousePressEvent(self, event: QMouseEvent):
        edge = self.getEdgeForMouseEvent(event)
        node = self.getNodeForMouseEvent(event)
        print("Edge: ", edge)
        print("Node: ", node)


class PateWindow(QDialog):
    def __init__(self, context: UIActionContext, parent=None):
        super().__init__(parent)
        self.context = context  # TODO: What is this for?

        g = FlowGraph()
        n1 = FlowGraphNode(g)
        n1.lines = ["foo"]
        g.append(n1)
        n2 = FlowGraphNode(g)
        n2.lines = ["bar"]
        g.append(n2)
        n1.add_outgoing_edge(BranchType.UnconditionalBranch, n2)

        self.flow_graph_widget = MyFlowGraphWidget(self, None, g)
        self.flow_graph_widget.setMinimumWidth(400)
        self.flow_graph_widget.setMinimumHeight(400)

        layout = QVBoxLayout()
        layout.addWidget(self.flow_graph_widget)
        self.setLayout(layout)


def launch_pate(context: UIActionContext):

    f = interaction.get_open_filename_input(
        "Run PATE",
        "PATE Run Configuration (*.run-config.json);;PATE Replay (*.replay)")
    print(f)
    if f.endswith(".run-config.json"):
        replay = False
        trace_file = os.path.join(os.path.dirname(f), 'lastrun.replay')
        fn = lambda ignore: pate.run_pate_config(f)
    elif f.endswith(".replay"):
        replay = True
        trace_file = None
        fn = lambda ignore: pate.run_replay(f)
    pt = PateThread(None, fn, replay=replay, trace_file=trace_file)

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

    GlobalArea.addWidget(lambda context: PateWidget('Pate Interaction'))

    UIAction.registerAction('Pate...')
    UIActionHandler.globalActions().bindAction('Pate...', UIAction(launch_pate))
    Menu.mainMenu('Plugins').addAction('Pate...', 'Pate', True)

    #UIAction.registerAction('Pate...')
    #UIActionHandler.globalActions().bindAction('Pate...', UIAction(launch_pate))
    #Menu.mainMenu('Plugins').addAction('Pate...', 'Pate', True)


register()
