# Copyright 2023-2024, Galois Inc. All rights reserved.

from __future__ import annotations
import abc
import io
import json
import os
import pathlib
import pprint
import re
import shlex
import signal
import sys
import threading
from functools import reduce
from json import JSONDecodeError, JSONEncoder, JSONDecoder
from subprocess import Popen, PIPE, STDOUT, TimeoutExpired
from typing import IO, Any, Optional

# TODO: Get rid of these globals
pp = pprint.PrettyPrinter(indent=4)


class PateUserInteraction(abc.ABC):
    @abc.abstractmethod
    def ask_user(self, prompt: str, choices: list[str], replay_choice: Optional[str] = None) -> Optional[str]:
        pass

    @abc.abstractmethod
    def show_message(self, msg) -> None:
        pass

    @abc.abstractmethod
    def show_cfar_graph(self, graph: CFARGraph) -> None:
        pass


class PateWrapper:
    user: PateUserInteraction
    filename: os.PathLike
    pate_proc: Optional[Popen]
    trace_file: Optional[IO]
    last_cfar_graph: Optional[CFARGraph]

    def __init__(self, filename: os.PathLike,
                 user: PateUserInteraction,
                 config_callback=None
                 ) -> None:
        self.debug_io = False
        self.debug_json = False
        self.debug_cfar = False

        self.filename = filename
        self.user = user
        self.config_callback = config_callback

        self.pate_proc = None
        self.trace_file = None
        self.last_cfar_graph = None

        self.traceConstraintModeDone = threading.Event()

    def run(self) -> None:
        if self.filename.endswith(".run-config.json"):
            self._run_live()
        elif self.filename.endswith(".replay"):
            self._run_replay()
        else:
            self.user.show_message('ERROR: Unrecognized PATE run file type', self.filename)

    def _run_live(self):
        cwd = os.path.dirname(self.filename)
        self.config = load_run_config(self.filename)
        if not self.config:
            self.user.show_message('ERROR: Failed to load PATE run config from', self.filename)
            return
        original: str = self.config.get('original')
        patched: str = self.config.get('patched')

        # Pate needs the actual binary, not a binja db file. This is a hack that will only work when the exe is in the
        # same directory as the db file and has teh same basename.
        # TODO: Make this more robust. Either find the exe from the db file, or have the gui fond the db from the exe.
        original = original.removesuffix(".bndb")
        patched = patched.removesuffix(".bndb")

        raw_args = self.config.get('args')
        args = shlex.split(' '.join(raw_args))
        # We use a helper script to run logic in the user's shell environment.
        script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "run-pate.sh")
        # Need -l to make sure user's env is fully setup (e.g. access to docker and ghc tools).
        allArgs = ['/bin/bash', '-l', script, '-o', original, '-p', patched, '--json-toplevel', '--add-trace-constraints'] + args
        print('Pate command line: ' + ' '.join(allArgs))
        with open(os.path.join(cwd, "lastrun.replay"), "w", encoding='utf-8') as trace:
            with Popen(allArgs,
                       cwd=cwd,
                       stdin=PIPE, stdout=PIPE,
                       stderr=STDOUT,
                       text=True, encoding='utf-8',
                       close_fds=True,
                       # Create a new process group, so we can kill it cleanly
                       preexec_fn=os.setsid
                       ) as proc:

                self.pate_proc = proc
                self.trace_file = trace
                self.user.replay = False

                # Write config to replay file before adding cwd
                json.dump(self.config, trace)
                trace.write('\n')
                self.config['cwd'] = cwd

                self.command_loop()

    def _run_replay(self):
        cwd = os.path.dirname(self.filename)
        with Popen(['cat', self.filename],
                   cwd=cwd, stdin=None, stdout=PIPE, text=True, encoding='utf-8',
                   close_fds=True,
                   # Create a new process group, so we can kill it cleanly
                   preexec_fn=os.setsid
                   ) as proc:

            self.pate_proc = proc
            self.trace_file = None
            self.user.replay = True

            # Read config from replay file
            self.config = self.next_json()
            self.config['cwd'] = cwd

            self.command_loop()

    def cancel(self) -> None:
        if self.pate_proc:
            # Closing input should cause PATE process to exit
            if self.pate_proc.stdin:
                self.pate_proc.stdin.close()
            try:
                self.pate_proc.wait(3)
            except TimeoutExpired:
                # Orderly shutdown did not work, kill the process group
                print('KILLING PATE Process')
                os.killpg(self.pate_proc.pid, signal.SIGKILL)
            self.pate_proc = None


    def next_line(self) -> str:
        line = self.pate_proc.stdout.readline()
        if not line:
            raise EOFError
        if self.trace_file:
            # Write line to trace file for replay
            self.trace_file.write(line)
            self.trace_file.flush()
        return line

    def next_json(self, gotoPromptAfterNonJson=False):
        while True:
            line = self.next_line()
            if self.debug_io:
                print('From Pate: ')
                pp.pprint(line)
            try:
                rec = json.loads(line)
            except JSONDecodeError:
                # Output line and continue looking for a JSON record
                self.user.show_message(line.rstrip('\n'))
                if gotoPromptAfterNonJson:
                    self._command('goto_prompt')
                    # Skip lines till we get json
                    gotoPromptAfterNonJson = False
            else:
                return rec

    def _skip_lines_till(self, s: str) -> None:
        """Skip lines till EOF or line completely matching s (without newline)."""
        while True:
            line = self.next_line().rstrip('\n')
            self.user.show_message(line)
            if line == s:
                break

    def _command(self, cmd: str) -> None:
        if self.debug_io:
            print('Command to Pate: ', cmd)
        if self.pate_proc.stdin:
            print(cmd, file=self.pate_proc.stdin, flush=True)
        if self.trace_file:
            # Write line to trace file for replay
            self.trace_file.write('Command: ' + cmd + '\n')
            self.trace_file.flush()
        else:
            # Replay mode
            cmd = self.pate_proc.stdout.readline()
            # TODO: Check that cmd is same as arg?

    def extract_graph(self) -> CFARGraph:
        cfar_graph = CFARGraph()

        self._command('top')
        top = self.next_json()

        self.extract_graph_rec(top, [], None, cfar_graph, None, None, None)

        self .connect_divergence_nodes(cfar_graph)
        self .connect_synchronization_nodes(cfar_graph)

        self.prune_orphans(cfar_graph)

        self.markFocusNodes(cfar_graph)

        return cfar_graph

    def markFocusNodes(self, cfar_graph: CFARGraph) -> None:
        self._command('goto_prompt')
        rec = self.next_json()

        while True:
            this = rec.get('this')
            if this == '<Toplevel>':
                break

            # TODO: desc? Or use data?
            nodes = (n for n in cfar_graph.nodes.values() if n.desc == this)
            node = next(nodes, None)
            if next(nodes, None):
                print(f'WARNING: Multiple nodes match: {this}')

            if rec.get('trace_node_kind') == 'blocktarget':
                if node:
                    node.focus = True
            elif rec.get('trace_node_kind') == 'node':
                if node:
                    node.focus = True
                break

            self._command('up')
            rec = self.next_json()
        pass

    def connect_divergence_nodes(self, graph: CFARGraph):
        divergentNodes: set[CFARNode] = set()
        for n in graph.nodes.values():
            try:
                divergedAt = n.data['trace_node']['entry_body']['context']['divergedAt']
            except KeyError:
                continue
            if divergedAt:
                divergedAtId = get_graph_node_id(divergedAt)
                divergedAt_cfar_node = graph.get(divergedAtId)
                divergentNodes.add(divergedAt_cfar_node)
                divergedAt_cfar_node.addExit(n)

        # TODO: Replace string hacks with something more resilient.
        for n in divergentNodes:
            # Prune non-matching exits from divergedAt node
            parts = [e for e in n.exits if e.id.startswith(n.id)]
            n.exits = parts
            # Don't splice out the "fake" node. Breaks things when the one-sided analysis is empty.
            # for p in parts:
            #     for e in p.exits:
            #         n.addExit(e)
            #     p.exits = []

            if self.debug_cfar:
                print('CFAR ID (divergedAt):', n.id)
                print("Remaining exits:")
                for e in n.exits:
                    print('   ', e.id)

    def connect_synchronization_nodes(self, graph: CFARGraph):
        # TODO: Replace string hacks with something more resilient.
        for n in list(graph.nodes.values()):
            if (n.id.find(' vs ') >= 0
                    and isinstance(n.data, dict)
                    and n.data.get('trace_node_kind') == 'node'
                    and not graph.get_parents(n)):
                parts = n.id.split(' vs ')
                if len(parts) != 2:
                    print('WARNING: Did not get exactly two parts for CFAR synchronization node. Skipping:', id)
                else:
                    o_id = parts[0] + ' (original)'
                    o_node = graph.get(o_id)
                    p_id = parts[1] + ' (patched)'
                    p_node = graph.get(p_id)

                    if self.debug_cfar and (o_node or p_node):
                        print()
                        pp.pprint(n.data)
                        print('CFAR Synchronization node:', n.id)

                    if o_node:
                        o_node.addExit(n)
                        if self.debug_cfar:
                            print('   Original CFAR:', o_id)

                    if p_node:
                        p_node.addExit(n)
                        if self.debug_cfar:
                            print('   Patched CFAR:', p_id)

    def prune_orphans(self, graph: CFARGraph):
        roots = [n for n in graph.nodes.values() if n.id.startswith('Function entry ')]
        marked = {}
        def mark(n: CFARNode):
            if not marked.get(n):
                marked[n] = True
                for e in n.exits:
                    mark(e)
        for r in roots:
            mark(r)
        orphans = [n for n in graph.nodes.values() if not marked.get(n)]
        for n in orphans:
            # TODO: move this to a delete method
            if self.debug_cfar:
                print('CFAR prune: ', n.id)
            n.exits = []
            del graph.nodes[n.id]

        # orphans = []
        # while True:
        #     for n in graph.nodes.values():
        #         if not n.id.startswith('Function entry ') and not graph.get_parents(n):
        #             # Found an orphan
        #             orphans.append(n)
        #     for n in orphans:
        #         # TODO: move this to a delete method
        #         if self.debug_cfar:
        #             print('CFAR prune: ', n.id)
        #         n.exits = []
        #         del graph.nodes[n.id]
        #     if not orphans:
        #         # Done
        #         break

    def extract_graph_rec(self,
                          rec: dict,
                          path: list[int],
                          context: dict | None,
                          cfar_graph: CFARGraph,
                          cfar_parent: CFARNode | None,
                          cfar_exit: CFARNode | None,
                          ancestor_tnc: dict | None,
                          ) -> None:
        this = rec.get('this')
        this = this.replace('\n',' ')
        trace_node = rec.get('trace_node')

        if self.debug_cfar:
            print('\nJSON {}:'.format(path))
            pp.pprint(rec)

        if path == [48] and this.startswith('segment1+0x4120 (original) vs. segment1+0x3dd44 (patched) [ via: "transport_handler" (segment1+0x400c) ]'):
            pass

        # Hack to extract proof obligations (same form as eq cond)
        if len(path) == 2 and rec.get('node_kind') in {'condition_kind'}:
            for i,tnc in enumerate(rec['trace_node_contents']):
                content = tnc['content']
                if content.get('node_kind') == 'message' and tnc.get('pretty') == 'Simplified Predicate':
                    self._command(str(i))
                    childrec = self.next_json()
                    for ci, ctnc in enumerate(childrec['trace_node_contents']):
                        ccontent = ctnc['content']
                        if ctnc['pretty'] == 'Condition Traces':
                            eqCond = ConditionTrace(ccontent)
                            match this:
                                case 'Asserted':
                                    #print('Found asserted cond for ', cfar_parent.id)
                                    if cfar_parent.assertedConditionTrace:
                                        cfar_parent.assertedConditionTrace.update(ccontent)
                                    else:
                                        cfar_parent.assertedConditionTrace = ConditionTrace(ccontent)
                                case 'Equivalence Condition Assumed':
                                    #print('Found assumed cond for ', cfar_parent.id)
                                    if cfar_parent.assumedConditionTrace:
                                        cfar_parent.assumedConditionTrace.update(ccontent)
                                    else:
                                        cfar_parent.assumedConditionTrace = ConditionTrace(ccontent)

                    self._command('up')
                    # Consume result of up, but do not need it
                    ignore = self.next_json()
            # Don't go any deeper
            return

        # Hack to find counter-example trace for exit. Really need to restructure this whole method.
        if (len(path) == 4
            and len(rec.get('trace_node_contents', [])) >= 3
            and rec['trace_node_contents'][1].get('pretty') == 'Equivalence Counter-example'
            ):
            for tnc in rec['trace_node_contents']:
                if tnc.get('content', {}).get('traces', {}):
                    cfar_parent.addExitMetaData(cfar_exit, 'ce_event_trace', tnc['content'])
            # don't go any deeper
            return

        # Possibly create a CFAR Node for this rec.
        id = None
        existing_cfar_node = None
        cfar_node = None
        if rec['trace_node_kind'] == 'node':
            id = get_graph_node_id(trace_node)
            existing_cfar_node = cfar_graph.get(id)
            cfar_node = cfar_graph.add_node(id, this, rec)

            # Look for observable difference trace for this node
            for n in rec['trace_node_contents']:
                if n.get('pretty') == 'Observable difference found':
                    traceContent = rec['trace_node_contents'][n['index'] + 1]
                    cfar_node.observableDiffTrace = traceContent['content']
                    break

        elif rec['trace_node_kind'] == 'blocktarget':
            id = get_blocktarget_id(rec, context, cfar_parent)
            existing_cfar_node = cfar_graph.get(id)
            cfar_node = cfar_graph.add_node(id, this, rec)

            # connect block target (ie exit) to parent
            cfar_exit = cfar_node
            cfar_parent.addExit(cfar_node)

            # Look for event trace on this exit
            for tnc in  rec['trace_node_contents']:
                if tnc.get('content') and tnc['content'].get('traces', {}):
                    cfar_parent.addExitMetaData(cfar_exit, 'event_trace', tnc['content'])
                    break

            # Look for observable difference trace for this node
            for n in rec['trace_node_contents']:
                if n.get('pretty') == 'Observable difference found':
                    traceContent = rec['trace_node_contents'][n['index'] + 1]
                    cfar_parent.observableDiffTrace = traceContent['content']
                    break

            if self.debug_cfar:
                print('CFAR ID (parent):', cfar_parent.id)

        if self.debug_cfar:
            print('CFAR ID:', id)

        # If we created a top level node, update parent and context.
        if cfar_node and len(path) == 1:
            cfar_parent = cfar_node
            if existing_cfar_node:
                # Revisiting top level CFAR, reset exits
                if self.debug_cfar:
                    print('Revisiting CFAR, clearing exits:')
                    for e in cfar_node.exits:
                        print('   ', e.id)
                cfar_node.exits = []
                cfar_node.exit_meta_data = {}
            if rec['trace_node'].get('entry_body'):
                context = rec['trace_node']['entry_body']['context']

        # TODO: Hack for blocks requiring implicit exit. Could possibly also look for 'endcase' == 'MacawBlockEndCall'.
        # TODO: Ask Dan about this, but the resulting graph looks reasonable to me.
        if cfar_node and rec.get('trace_node_kind') == 'blocktarget' and rec.get('tag') == []:
            # Add block exit
            exit_id = get_exit_id(trace_node, context)
            # TODO: Better way to detect this?
            if not(exit_id.startswith('None') or exit_id.startswith('return_target')):
                exit_node = cfar_graph.add_node(exit_id, 'junk', {})
                cfar_node.addExit(exit_node)
                if self.debug_cfar:
                    print('CFAR ID (exit):', exit_id)

        for i, tnc in enumerate(rec['trace_node_contents']):
            child = tnc['content']
            if not child:
                continue

            if child.get('trace_node_kind') == 'instruction_trees':
                # Process instruction trees. Do not descend into child.
                if cfar_node and len(path) == 1:
                    # Top level CFAR, attach instruction tree.
                    cfar_node.instruction_trees = child['trace_node']
                    # if cfar_node.id == 'S1+0x40d4 in S1+0x400c(transport_handler)':
                    #     print('FNORT')
                    #     pp.pprint(child['trace_node'])
                if cfar_parent and cfar_exit and len(path) > 1:
                    # Exit CFAR
                    cfar_parent.addExitMetaData(cfar_exit, 'instruction_trees_to_exit', child['trace_node'])

            # TODO: Ask Dan about this filter.
            if ((len(path) == 0 and child.get('trace_node_kind') in {'node'})
                    or (len(path) == 1 and child.get('subtree_kind') in {'"blocktarget"'})
                    or (len(path) == 1 and child.get('node_kind') in {'condition_kind'})
                    or (len(path) == 2 and child.get('trace_node_kind') in {'blocktarget'})
                    # Look for counter-example trace
                    or (len(path) == 3 and rec.get('trace_node_kind') == 'blocktarget'
                        and child.get('trace_node_kind') == 'node')):
                self._command(str(i))
                childrec = self.next_json()
                # update with values from child. TODO: ask Dan about this?
                childrec.update(child)
                self.extract_graph_rec(childrec, path + [i], context, cfar_graph, cfar_parent, cfar_exit, tnc)
                self._command('up')
                # Consume result of up, but do not need it
                ignore = self.next_json()
            # else:
            #     if self.debug_cfar:
            #         print('CFAR skip child:')
            #         pp.pprint(child)

    def _ask_user_rec(self, prompt_rec: dict) -> str:
        # Read entry point choices
        prompt = prompt_rec['this']
        choices = list(map(get_choice_id, prompt_rec.get('trace_node_contents', [])))
        return self._ask_user(prompt, choices).strip()
        # Write line to trace file for replay

    def _ask_user(self, prompt: str, choices: list[str]) -> Optional[str]:
        replay_choice = None
        if self.trace_file is None:
            replay_line = self.pate_proc.stdout.readline()
            if replay_line.startswith('User choice: '):
                replay_choice = replay_line[len('User choice: '):].strip()

        choice = self.user.ask_user(prompt, choices, replay_choice).strip()

        if self.trace_file:
            self.trace_file.write('User choice: ' + choice + '\n')
            self.trace_file.flush()
        return choice

    def command_loop(self):
        try:
            if self.config_callback:
                self.config_callback(self.config)
            rec = self.next_json()
            self._command('goto_prompt')
            while self.command_step():
                pass
            # Enter trace constraint processing mode
            self.traceConstraintModeDone.wait()
            self.user.show_message("Pate finished")
        except EOFError:
            self.user.show_message("Pate terminated unexpectedly")
            return False

    def command_step(self):
        # Process one json record from pate
        rec = self.next_json(gotoPromptAfterNonJson=True)
        return self.process_json(rec)

    def process_json(self, rec):

        if self.debug_json:
            print('\nProcessing JSON:')
            pp.pprint(rec)

        if isinstance(rec, dict) and rec.get('this') == 'Regenerate result with new trace constraints?':
            # Finish detected
            self.user.show_message('\nProcessing verification results ...\n')
            self.processFinalResult()
            return False

        elif isinstance(rec, dict) and rec.get('this') and rec.get('trace_node_kind'):
            # Prompt User
            if (not rec.get('this') == 'Choose Entry Point'
                    and isBlocked(rec)):
                # Extract flow graph
                cfar_graph = self.extract_graph()
                if cfar_graph:
                    #print('Update last cfar graph')
                    self.last_cfar_graph = cfar_graph
                    self.user.show_cfar_graph(cfar_graph)
                # Go back to prompt
                self._command('goto_prompt')
                rec = self.next_json()
            choice = self._ask_user_rec(rec)
            self._command(choice)

        elif isinstance(rec, dict) and rec.get('error'):
            self.show_message('error: ' + rec['error'])
            self._command('goto_prompt')

        else:
            # Message(s)
            self.show_message(rec)

        return True

    def processFinalResult(self, traceConstraints: Optional[list[tuple[TraceVar, str, str]]] = None, cfarNode: CFARNode = None):
        # TODO: add option to do with respect to a cfar node in which case missing should clear eq cond data?
        self._command('up')
        rec = self.next_json()
        # isinstance(rec, dict) and rec.get('trace_node_kind') == 'final_result':
        # Find the last "Toplevel Result"
        lastTopLevelResult = None
        for tnc in rec['trace_node_contents']:
            if tnc.get('pretty') == "Toplevel Result":
                lastTopLevelResult = tnc
        with io.StringIO() as out:
            if not lastTopLevelResult:
                out.write(f'No equivalence conditions found\n')
            else:
                eqconds = lastTopLevelResult.get('content', {}).get('eq_conditions', {}).get('map')
                if eqconds:
                    # Found eq conditions
                    for item in eqconds:
                        node = item['key']
                        eqcond = item['val']

                        node_id = get_graph_node_id(node)

                        if self.last_cfar_graph:
                            cfar_node = self.last_cfar_graph.get(node_id)
                            if cfar_node.equivalenceConditionTrace:
                                cfar_node.equivalenceConditionTrace.update(eqcond, traceConstraints)
                            else:
                                cfar_node.equivalenceConditionTrace = ConditionTrace(eqcond, traceConstraints)

                        # print('CFAR id:', node_id)

                        # out.write(f'Equivalence condition for {node_id}\n')
                        # pprint_symbolic(out, predicate)
                        # out.write('\n')

                        # out.write('\nTrace True\n')
                        # pprint_node_event_trace(trace_true, 'True Trace', out=out)

                        # out.write('\nTrace False\n')
                        # pprint_node_event_trace(trace_false, 'False Trace', out=out)

                else:
                    # Hack to handle case where constraints were unsatisfiable
                    ect = cfarNode.equivalenceConditionTrace
                    ect.trace_true = False
                    ect.trace_false = False
                    ect.traceConstraints = traceConstraints
                    ect.predicate = ect.unconstrainedPredicate

            self.user.show_message(out.getvalue())
        if self.last_cfar_graph:
            self.user.show_cfar_graph(self.last_cfar_graph)
        self._command('goto_prompt')
        rec = self.next_json()

    def getReplayTraceConstraints(self) -> Optional[list[tuple[TraceVar, str, str]]]:
        if self.trace_file is None:
            # Read constraints from replay file
            # Replay need to do this ahead of time to populate trace constraint dialog.
            # Doing it here for now so replay works for debugging.
            replay_line = self.pate_proc.stdout.readline()
            if replay_line.startswith('Trace Constraints: '):
                replay_line = replay_line[len('Trace Constraints: '):].strip()
                # Parse JSON and return it
                traceConstraints = json.loads(replay_line, object_hook=traceConstraintsJSONObjectHook)
                # TODO: replace top level list[3] with tuple[3]
                traceConstraints = [tuple(x) for x in traceConstraints]
                #print('Replay constraints:', traceConstraints)
                return traceConstraints
        return None

    def processTraceConstraints(self, traceConstraints: list[tuple[TraceVar, str, str]], cfarNode: CFARNode) -> None:

        self.user.show_message('\nProcessing trace constraints ...\n')

        if self.trace_file:
            # Write constraints to trace file for use in replay mode
            tcl = [f'{tc[0].pretty} {tc[1]} {tc[2]}' for tc in traceConstraints]
            self.trace_file.write('Trace Constraints: ')
            json.dump(traceConstraints, self.trace_file, cls=TraceConstraintsJSONEncoder)
            self.trace_file.write('\n')
            self.trace_file.flush()

        # TODO: infrastructure to do this in the background on same thread as command loop
        with io.StringIO() as out:
            # input "[ [ { \"var\" : { \"symbolic_ident\" : 0 }, \"op\" : \"EQ\", \"const\" : \"128\"} ] ]"
            # TODO: Handle multiple nodes in final result
            out.write(r'input "[')
            # TODO: Handle multiple eq conds
            out.write(r'[')
            for i, tc in enumerate(traceConstraints):
                if i > 0:
                    out.write(r',')
                out.write(r'{\"var\":{\"symbolic_ident\":')
                # symbolic_ident
                out.write(str(tc[0].symbolic_ident))
                out.write(r'},\"op\":\"')
                # op
                out.write(tc[1])
                out.write(r'\",\"const\":\"')
                # int const
                out.write(str(tc[2]))
                out.write(r'\"}')
            out.write(r']')
            out.write(r']"')
            verifierTraceConstraintInput = out.getvalue()

        #print('verifierTraceConstraintInput:', verifierTraceConstraintInput)
        #self.debug_io = True
        self._command('0')
        # TODO: Consider generalizing command_loop rather than this processing?
        #print('waiting for constraint prompt')
        while True:
            rec = self.next_json()
            if isinstance(rec, dict) and rec['this'] == 'Waiting for constraints..':
                break
            else:
                self.show_message(rec)
        self._command(verifierTraceConstraintInput)
        #print('waiting for regenerate result prompt')
        while True:
            rec = self.next_json()
            if isinstance(rec, dict) and rec['this'] == 'Regenerate result with new trace constraints?':
                break
            else:
                self.show_message(rec)
        #print('waiting for constraint prompt')
        self.processFinalResult(traceConstraints, cfarNode)

    def show_message(self, rec: Any):
        if isinstance(rec, list):
            for m in rec:
                self.user.show_message("Processing ... " + get_choice_id(m))
        elif isinstance(rec, dict) and rec.get('message'):
            self.user.show_message(rec['message'])
        else:
            self.user.show_message(str(rec))


class ConditionTrace:

    def __init__(self, raw: dict, traceConstraints: Optional[list[tuple[TraceVar, str, str]]] = None):
        self.unconstrainedPredicate = raw['predicate']
        self.traceConstraints = traceConstraints
        self.predicate = None
        self.trace_true = None
        self.trace_false = None
        self.trace_footprint = None
        self.update(raw)
        # Debug stub
        # vars = extractTraceVars(self)
        # pass

    def update(self, raw:dict, traceConstraints: Optional[list[tuple[TraceVar, str, str]]] = None):
        self.traceConstraints = traceConstraints
        self.predicate = raw['predicate']
        self.trace_true = raw['trace_true']
        self.trace_false = raw['trace_false']
        self.trace_footprint = raw['trace_footprint']


class TraceCollection:

    def __init__(self, desc: str, raw: dict):
        self.desc = desc
        self.allTraces = raw['all_traces']
        self.cellTraces = self._extractTraceMap(raw['trace_map_cells'])
        self.regTraces = self._extractTraceMap(raw['trace_map_regs'])

    def _extractTraceMap(self, raw: dict):
        traceMap = []
        for kv in raw['map']:
            traces = [self.allTraces[ti] for ti in kv['val']]
            traceMap.append((kv['key'], traces))
        return traceMap

    def maxNumTraces(self):
        return max(reduce(max, map(lambda x: len(x[1]), self.regTraces)),
                   reduce(max, map(lambda x: len(x[1]), self.cellTraces)))


class WideningInfo:

    def __init__(self, raw: dict):
        self.postdomain = None
        self.valueTraceCollection = None
        self.equalityTraceCollection = None
        self.sharedEnv = None

        if raw.get('name') == 'Equivalence Counter-example Traces':
            for ltv in raw['contents']:
                if ltv['label'] == 'Postdomain' and ltv['type'] == 'domain':
                    self.postdomain = ltv['value']
                elif ltv['label'] == 'Value' and ltv['type'] == 'trace_collection':
                    self.valueTraceCollection = TraceCollection('Value', ltv['value'])
                elif ltv['label'] == 'Equality' and ltv['type'] == 'trace_collection':
                    self.equalityTraceCollection = TraceCollection('Equality', ltv['value'])
            self.sharedEnv = raw['shared_env']

    def prettyLoc(self, loc: dict) -> str:
        id = loc.get('ptr',{}).get('offset',{}).get('symbolic_ident')
        if not id:
            return '1 ' + str(loc)
        matches = [x['symbolic_expr'] for x in self.sharedEnv if x['symbolic_ident'] == id]
        if not matches:
            return '2 ' + str(loc)
        with io.StringIO() as out:
            pprint_symbolic(out, matches[0])
            return out.getvalue()


class CFARNode:
    exits: list[CFARNode]

    def __init__(self, id: str, desc: str, data: dict):
        self.id = id
        (self.original_addr, self.patched_addr) = get_cfar_addr(id)
        self.exits = []
        self.exit_meta_data = {}
        self.desc = desc
        self.data = data
        self.predomain = None
        self.postdomain = None
        self.external_postdomain = None
        self.addr = None
        self.focus = False
        self.traceConstraints = None
        self.instruction_trees = None
        self.wideningInfo = None
        self.observableDiffTrace = None
        self.equivalenceConditionTrace = None
        self.assertedConditionTrace = None
        self.assumedConditionTrace = None

        # After default initializations above, update the node
        self.update_node(desc, data)

    def update_node(self, desc: str, data: dict):
        self.desc = desc
        self.data = data
        self.predomain = get_domain(data, 'Predomain')
        self.postdomain = get_domain(data, 'Postdomain')
        self.external_postdomain = get_domain(data, 'ExternalPostDomain')

        for cw in data.get('trace_node_contents', []):
            content = cw['content']
            if content and content.get('name') == 'Equivalence Counter-example Traces':
                self.wideningInfo = WideningInfo(content)

    def addExit(self, node: CFARNode) -> bool:
        """Add a block exit to node if new.

        Returns True if added, False if already a block exit."""
        if not self.isExit(node):
            self.exits.append(node)
            return True
        else:
            return False

    def addExitMetaData(self, exit, key, val):
        # Create meta data dict for this exit if it does not already exist
        if not self.exit_meta_data.get(exit):
            self.exit_meta_data[exit] = {}
        # Check for overwrite
        if self.exit_meta_data[exit].get(key):
            # TODO: Is this a problem?
            #warnings.warn('Meta data already exists. Overwriting.')
            pass
        # Add the meta data
        self.exit_meta_data[exit][key] = val

    def isExit(self, node: CFARNode) -> bool:
        return node in self.exits

    def pprint(self, pre: str = ''):
        print(f'{pre}CFAR Node: {self.id}')
        print(f'{pre}desc: {self.desc}')
        # if self.predicate:
        #     sys.stdout.write('Equivalence Condition: ')
        #     pprint_symbolic(sys.stdout, self.predicate)
        #     sys.stdout.write('\n')
        self.pprint_node_contents(pre, show_ce_trace=True)
        # if self.instruction_trees:
        #     pprint_node_inst_tree(self.instruction_trees.get('original'), 'Original inst tree: ')
        #     pprint_node_inst_tree(self.instruction_trees.get('patched'), 'Patched inst tree: ')
        print()
        #print('data:')
        #pp.pprint(self.data)

    def pprint_node_contents(self, pre: str = '', out: IO = sys.stdout, show_ce_trace: bool = False):
        self.pprint_node_domain(pre, out, show_ce_trace)
        if show_ce_trace:
            for n in self.exits:
                out.write(f'{pre}Exit: {n.id}\n')
                if self.exit_meta_data.get(n,{}).get('ce_event_trace'):
                    pprint_node_event_trace(self.exit_meta_data[n]['ce_event_trace'], 'Counter-Example Trace', pre + '  ', out)
                elif self.exit_meta_data.get(n, {}).get('event_trace'):
                    pprint_node_event_trace(self.exit_meta_data[n]['event_trace'], 'Witness Trace', pre + '  ', out)

    def pprint_node_domain(self, pre: str = '', out: IO = sys.stdout,
                           show_ce_trace: bool = False):
        if self.predomain:
            out.write(f'{pre}Predomain:\n')
            pprint_domain(self.predomain, pre + '  ', out)
        # TODO: Drop for Jan demo
        # if self.postdomain:
        #     out.write(f'{pre}postdomain (internal):')
        #     pprint_domain(self.postdomain, pre + ' ', out)
        if self.external_postdomain:
            out.write(f'{pre}Postdomain:\n')
            pprint_domain(self.external_postdomain, pre + '  ', out)



class CFARGraph:
    nodes: dict[str, CFARNode]

    def __init__(self):
        self.nodes = {}

    def get(self, id):
        return self.nodes.get(id)

    def getFocusNodes(self):
        return [n for n in self.nodes.values() if n.focus]

    def getEqCondNodes(self):
        nodes = []
        for n in self.nodes.values():
            if n.equivalenceConditionTrace:
                nodes.append(n)
        return nodes

    def add_node(self, id: str, desc: str, data) -> CFARNode:
        """Add node, creating if node with ID does not exist."""

        node = self.nodes.get(id)
        if not node:
            node = CFARNode(id, desc, data)
            self.nodes[node.id] = node
        else:
            # update with most recent data
            node.update_node(desc, data)
        return node

    def pprint(self):
        print('Dumping CFAR graph...')
        for n in self.nodes.values():
            n.pprint()


    def get_parents(self, node: CFARNode) -> list[CFARNode]:
        parents = []
        for n in self.nodes.values():
            for e in n.exits:
                if node == e:
                    parents.append(n)
        return parents


class TraceVar:
    def __init__(self, prefix: str, kind: str, raw: dict):
        self.prefix = prefix
        self.kind = kind
        self.raw = raw
        self.pretty = 'unknown'
        self.numBits = 0
        self.type = None
        self.symbolic_ident = None

        match self.kind:
            case 'reg_op':
                with io.StringIO() as out:
                    out.write(prefix)
                    out.write(" ")
                    pprint_reg_op(self.raw, out=out)
                    self.pretty = out.getvalue()
                self.type = self.raw['val']['offset']['type']
                # TODO: parse numBits from type
                self.numBits = 32
            case 'mem_op':
                mem_op = raw['snd']
                with io.StringIO() as out:
                    out.write(prefix)
                    out.write(" ")
                    out.write(f'{get_addr_id(raw["fst"])}: {mem_op["direction"]} {get_value_id(mem_op["addr"])} ')
                    self.pretty = out.getvalue()
                offset = mem_op['value']['offset']
                if isinstance(offset, dict):
                    self.symbolic_ident = offset['symbolic_ident']
                    self.type = offset['type']
                self.numBits = mem_op['size'] * 8


class TraceConstraintsJSONEncoder(JSONEncoder):
    def default(self, o):
        if isinstance(o, TraceVar):
            return {'class': 'TraceVar',
                    'prefix': o.prefix,
                    'kind': o.kind,
                    'raw': o.raw}
        else:
            return super().default(o)


def traceConstraintsJSONObjectHook(d: dict):
    if d.get('class') == 'TraceVar':
        return TraceVar(d['prefix'], d['kind'], d['raw'])
    else:
        return d


def extractTraceVars(condition: ConditionTrace) -> list[TraceVar]:
    footprint = condition.trace_footprint
    #pprint.pprint(condition.trace_footprint)
    traceVars = []
    # for r in footprint['original']['fp_initial_regs']['reg_op']['map']:
    #     traceVars.append(TraceVar('original', 'reg_op', r))
    for r in footprint['original']['fp_mem']:
        traceVars.append(TraceVar('original', 'mem_op', r))
    # for r in footprint['patched']['fp_initial_regs']['reg_op']['map']:
    #     traceVars.append(TraceVar('patched', 'reg_op', r))
    for r in footprint['patched']['fp_mem']:
        traceVars.append(TraceVar('patched', 'mem_op', r))
    # TODO: sort by instruction addr, but reverse seems to work for now
    traceVars.reverse()
    return traceVars

def get_cfar_addr(cfar_id: str) -> tuple[Optional[int], Optional[int]]:
    """Get CFAR original and patched address"""
    parts = cfar_id.split(' vs ')
    if len(parts) == 2:
        # diff addr for orig and patch
        return get_cfar_addr_1(parts[0]), get_cfar_addr_1(parts[1])
    elif len(parts) == 1:
        m = re.match(r'(.*)\(original\)', parts[0])
        if m:
            # only orig addr
            return get_cfar_addr_1(m.group(1)), None
        m = re.match(r'(.*)\(patched\)', parts[0])
        if m:
            # only patch addr
            return (None, get_cfar_addr_1(m.group(1)))
        # same addr for both
        addr = get_cfar_addr_1(parts[0])
        return addr, addr
    else:
        return None, None


def get_cfar_addr_1(cfar_id:str) -> Optional[int]:

    # First addr
    m = re.search(r'S[0-9A-Fa-f]+\+(0x[0-9A-Fa-f]+)', cfar_id)
    if m:
        addr = m.group(1)
        return int(addr, 16)

    return None


def get_addr_id(a: dict):
    base = a['base']
    offset = a['offset']
    return 'S{}+{}'.format(base, offset)


def get_value_id(v):
    if isinstance(v, dict):
        region = v['region']
        offset = v['offset']
        if region == 0:
            return offset
        elif region == 1:
            return f'Stack Slot: {offset}'
        else:
            return f'({region}, {offset})'
    else:
        return str(v)


def get_func_id(func: dict):
    if func is None:
        return 'None'
    sym = func.get('symbol')
    addr_id = get_addr_id(func['address'])
    if sym:
        return f'{addr_id}({sym})'
    else:
        return addr_id


def get_ref_id(r: dict):
    if r is None:
        return "None"
    addr = r['address']
    func = r['function']
    if addr == func['address']:
        return get_func_id(func)
    else:
        return '{} in {}'.format(get_addr_id(addr), get_func_id(func))


def get_block_id(b: dict, context: dict = None):
    o = b.get('original')
    p = b.get('patched')

    if o == p:
        # Patched and original the same
        id = get_ref_id(o)
    elif p is None:
        id = '{} (original)'.format(get_ref_id(o))
    elif o is None:
        id = '{} (patched)'.format(get_ref_id(p))
    else:
        id = '{} vs {}'.format(get_ref_id(o), get_ref_id(p))

    if context:
        ancestors = context['ancestors']
        id += get_ancestors_id(ancestors)

    return id


def get_target_id(t: dict):
    if not isinstance(t, dict):
        # TODO: Is this reasonable?
        return t

    match t['endcase']:
        case 'MacawBlockEndCall':
            target = get_ref_id(t['target'])
            if t['return'] is None:
                return 'Tail call {}'.format(target)
            else:
                ret = get_ref_id(t['return'])
                return 'Call {} returns to {}'.format(target, ret)
        case 'MacawBlockEndBranch':
            target = get_ref_id(t['target'])
            return 'Branch {}'.format(target)
        case 'MacawBlockEndJump':
            target = get_ref_id(t['target'])
            return 'Jump {}'.format(target)
        case _:
            return t


def get_return_id(t: dict):
    if not isinstance(t, dict):
        # TODO: Is this reasonable?
        return t

    match t['endcase']:
        case 'MacawBlockEndCall':
            return get_ref_id(t['return'])
        case 'MacawBlockEndBranch':
            return get_ref_id(t['target'])
        case 'MacawBlockEndJump':
            return get_ref_id(t['target'])
        case _:
            return t


def get_exit_id(r: dict, context: dict = None):
    o = r.get('original')
    p = r.get('patched')

    if o:
        o = get_return_id(o)
        #o = get_ref_id(o['return'])
    if p:
        p = get_return_id(p)
        #p = get_ref_id(p['return'])

    if o == p:
        id =  o
    elif p is None:
        id = '{} (original)'.format(o)
    elif o is None:
        id = '{} (patched)'.format(p)
    else:
        id = '{} vs {}'.format(o, p)

    if context:
        ancestors = context['ancestors']
        id += get_ancestors_id(ancestors)

    return id


def get_return_target_id(selector: str, parent: CFARNode):
    gn = parent.data['trace_node']
    match gn['graph_node_type']:
        case 'entry':
            func = gn['entry_body']['blocks'][selector]['function']
            return 'Return from ' + get_func_id(func)
        case _:
            return 'return_target'


def get_blocktarget_id(rec: dict, context: dict = None, parent: CFARNode = None):
    b = rec['trace_node']
    o = b.get('original')
    p = b.get('patched')

    if o:
        o = get_target_id(o)
    if p:
        p = get_target_id(p)

    if o == 'return_target':
        o = get_return_target_id('original', parent)
    if p == 'return_target':
        p = get_return_target_id('patched', parent)

    if o == p:
        # Patched and original the same
        id = o
    elif p is None:
        id = '{} (original)'.format(o)
    elif o is None:
        id = '{} (patched)'.format(p)
    else:
        id = '{} vs {}'.format(o, p)

    anc_id = ''
    if context:
        ancestors = context['ancestors']
        id += get_ancestors_id(ancestors)
        # TODO: Handle different length ancestor paths for original and patched
        # if (isinstance(o, dict) and isinstance(p, dict)):
        #     # Add return address to ancestors
        #     # TODO: undo this
        #     #new_ancestor = {'original': o['return'], 'patched': p['return']}
        #     #ancestors = [new_ancestor] + ancestors
        #     id += get_ancestors_id(ancestors)

    return id

def get_return_function_id(b: dict, context: dict = None):
    # TODO handle function and symbol
    o = b.get('original')
    p = b.get('patched')
    if o == p:
        # Patched and original the same
        id = get_func_id(o)
    elif p is None:
        id = '{} (original)'.format(get_func_id(o))
    elif o is None:
        id = '{} (patched)'.format(get_func_id(p))
    else:
        id = '{} vs {}'.format(get_func_id(o), get_func_id(p))

    if context:
        ancestors = context['ancestors']
        id += get_ancestors_id(ancestors)

    return id


def get_ancestors_id(ancs: list):
    id = ''
    for addr in ancs:
        id += ' <- ' + get_block_id(addr)
    return id


def get_entry_node_id(en: dict):
    return get_block_id(en['blocks'], en['context'])


def get_return_node_id(en: dict):
    return get_return_function_id(en['functions'], en['context'])


def get_graph_node_id(gn: dict):
    match gn['graph_node_type']:
        case 'entry':
            id = get_entry_node_id(gn['entry_body'])
            if gn['entry_body']['type'] == 'function_entry':
                id = 'Function entry ' + id
            return id
        case 'return':
            return 'Return from ' + get_return_node_id(gn['return_body'])
        case _:
            return str(dict)


def get_trace_node_id(tnc: dict):
    """Only use this for GUI menus as it includes the tag if present."""
    if not tnc.get('trace_node'):
        return str(tnc)

    # TODO: Hack to deal with pickManyChoice
    if tnc.get('trace_node_kind') == 'pickManyChoice':
        return tnc['trace_node']

    graph_node_id = get_graph_node_id(tnc['trace_node'])
    if tnc.get('tag'):
        return '{} ({})'.format(graph_node_id, tnc['tag'])
    else:
        return graph_node_id


def get_choice_id(rec: dict):
    content = rec['content']
    index = rec['index']
    indent = rec['indent']
    # 'more' is set when there are more elements to display in a subtree, but they haven't been sent/printed. It means
    # you need to navigate to that subtree explicitly in order to see all the elements.
    more = rec['more']  # TODO: Ask Dan about this
    pretty = rec['pretty']

    msg = str(index) + ": "
    for i in range(indent):
        msg += " "
    msg += pretty.replace('\n',' ')

    if more:
        msg += " more results..."

    # if choice.get('trace_node') and choice.get('trace_node_kind') == 'choice':
    #     return get_trace_node_id(choice['trace_node'])
    # if not content.get('trace_node') and content.get('tag') and content.get('trace_node_kind') == 'choice':
    #     return content['tag']
    # if content.get('trace_node') and content.get('trace_node_kind') == 'blocktarget':
    #     return get_blocktarget_id(content['trace_node'])
    # if content.get('trace_node') and content.get('trace_node_kind') == 'node':
    #     return get_trace_node_id(content)
    # if content.get('trace_node') and content.get('trace_node_kind') == 'entrynode':
    #     return get_entry_node_id(content['trace_node'])
    # if content.get('message'):
    #     # TODO: Ask dan about quotes in 'subtree_kind' values. Intentional?
    #     return content['message']
    # if content.get('node_kind'):
    #     # TODO: Ask dan about quotes in 'subtree_kind' values. Intentional?
    #     return content['node_kind']

    return msg


def get_domain(rec: dict, kind: str):
    for cw in rec.get('trace_node_contents', []):
        content = cw['content']
        if content and content.get('kind') == kind:
            return content['abstract_domain']


def isBlocked(rec: dict):
    if not (isinstance(rec, dict)
            and rec.get('trace_node_contents')
            and rec.get('trace_node_blocked')):
        return False

    for c in rec.get('trace_node_contents', []):
        if not (isinstance(c, dict) and c.get('blocked') is False):
            return False

    return True


def pprint_domain(d: dict, pre: str = '', out: IO = sys.stdout):
    for k,v in d.items():
        match k:
            case 'eq_domain':
                pprint_eq_domain(v, pre, out)
            case 'val_domain':
                pprint_val_domain(v, pre, out)
            case _:
                out.write(f'{pre}Unknown domain kind "{k}": {v}/n')


def pprint_eq_domain(v, pre: str = '', out: IO = sys.stdout):
    for k, v in v.items():
        match k:
            case 'registers':
                pprint_eq_domain_registers(v, pre, out)
            case 'pointers':
                pprint_eq_domain_memory('Pointer', v, pre, out)
            case 'stack_slots':
                pprint_eq_domain_memory('Stack Slot', v, pre, out)
            case 'memory':
                pprint_eq_domain_memory('Memory', v, pre, out)
            case 'stack':
                pprint_eq_domain_memory('Stack', v, pre, out)
            case 'max_region':
                # TODO: Ask Dan about these. They appear in trace pre/post conditions
                out.write(f'{pre}Max Region: {v}\n')
            case 'stack_base':
                # TODO: Ask Dan about these. They appear in trace pre/post conditions
                out.write(f'{pre}Stack Base: {v}\n')
            case _:
                out.write(f'{pre}Unknown eq domain "{k}": {v}\n')


def pprint_eq_domain_registers(v, pre: str = '', out: IO = sys.stdout):
    for m in v['map']:
        if m.get('pred') is True:
            # TODO: does this apply to pre/post domains and trace conditions?
            pass
        elif m['val'] is not True:
            name = get_reg_desc(m["key"])
            if not name.startswith('_'):
                out.write(f'{pre}Register: {get_reg_desc(m["key"])}')
                if m['val']:
                    out.write(f' val: {m["val"]}')
                out.write('\n')


def get_reg_desc(r):
    match r:
        case {'arch_reg': name}:
            return str(name)
        case {'reg': name}:
            return str(name)
        case _:
            return str(r)


def pprint_eq_domain_memory(mem_kind, pv, pre: str = '', out: IO = sys.stdout):
    logop = pv.get('kind')
    if logop in ['disj', 'conj']:  # TODO: Deal with this difference?
        for p in pv['predmap']:
            if p.get('pred') == True:
                # TODO: does this apply to pre/post domains and trace conditions?
                continue
            pv = p['val']
            region = pv["ptr"]["region"]
            offset = pv["ptr"]["offset"]
            out.write(f'{pre}{mem_kind}: ')
            if region == 0 or (region == 1 and mem_kind in {'Stack', 'Stack Slot'}):
                pprint_symbolic(out, pv["ptr"]["offset"])
            else:
                out.write('(')
                pprint_symbolic(out, pv["ptr"]["region"])
                out.write(', ')
                pprint_symbolic(out, pv["ptr"]["offset"])
                out.write(')')
            #out.write(f' {v["endianness"]}[{v["width"]}]')
            # TODO: Drop for Jan demo.
            # if p['pred'] != True:
            #     # TODO: Ask Dan about this
            #     out.write('\n    pred: ')
            #     pprint_symbolic(out, p['pred'])
            out.write('\n')
    else:
        out.write(f'{pre}Unknown domain memory logical op "{logop}": {pv}\n')


def pprint_node_event_trace(trace, label: str, pre: str = '', out: IO = sys.stdout):
    out.write(f'{pre}{label} Domain:\n')
    pprint_node_event_trace_domain(trace, pre + '  ', out)

    out.write(f'{pre}{label} (original):\n')
    pprint_node_event_trace_original(trace, pre + '  ', out)

    out.write(f'{pre}{label} (patched):\n')
    pprint_node_event_trace_patched(trace, pre + '  ', out)


def pprint_node_event_trace_domain(trace, pre: str = '', out: IO = sys.stdout):
    precond = trace.get('precondition') if trace else None
    postcond = trace.get('postcondition') if trace else None
    # [20240509 JCC] Dan says to only show the domain for a trace if postcondition is present.
    # [20241119 JCC] More detail from Dan: I don't think there's much value in it for concrete
    # traces, since it can be deduced by looking at the differences between the traces. i.e.
    # the precondition tells you which locations were assumed equal initially, which you can
    # tell fairly easily in a concrete trace by looking at differences in the initial state.
    # It's only potentially relevant when you have a post-condition, since it's otherwise
    # possibly not obvious why a given trace violates the post-condition, which is why I
    # think we included it in the first place.
    if not (postcond):
        out.write(f'{pre}No Post Condition.\n')
        return

    if precond:
        out.write(f'{pre}Precondition:\n')
        pprint_eq_domain(precond, pre + '  ', out)
    if postcond:
        out.write(f'{pre}Postcondition:\n')
        pprint_eq_domain(postcond, pre + '  ', out)


def pprint_node_event_trace_original(trace, pre: str = '', out: IO = sys.stdout):
    if not trace:
        out.write(f'{pre}No trace\n')
        return

    pprint_event_trace(trace.get('traces', {}).get('original'),
                       other_et=trace.get('traces', {}).get('patched'),
                       pre=pre,
                       out=out
                       )


def pprint_node_event_trace_patched(trace, pre: str = '', out: IO = sys.stdout):
    if not trace:
        out.write(f'{pre}No trace\n')
        return
    pprint_event_trace(trace.get('traces', {}).get('patched'),
                       other_et=trace.get('traces', {}).get('original'),
                       pre=pre,
                       out=out
                       )


def pprint_event_trace(et: dict, pre: str = '', out: IO = sys.stdout, other_et: dict = None):
    if not et:
        out.write(f'{pre}No trace\n')
        return

    no_prune = []
    if other_et:
        for reg in other_et['initial_regs']['reg_op']['map']:
            ppval = get_value_id(reg['val'])
            key: dict = reg['key']
            if not ppval.startswith('0x0:'):
                no_prune.append(key)

    pprint_event_trace_initial_reg(et['initial_regs'], pre, out, no_prune)
    pprint_event_trace_instructions(et['events'], pre, out)


def pprint_event_trace_initial_reg(initial_regs: dict, pre: str = '', out: IO = sys.stdout, no_prune: list = []):
    """Pretty print an event trace's initial registers."""
    out.write(f'{pre}Initial Register Values (non-zero):\n')
    pprint_reg_ops(initial_regs['reg_op'], pre + '  ', out, True, no_prune)


def pprint_reg_ops(reg_op: dict, pre: str = '', out: IO = sys.stdout, prune_zero: bool = False, no_prune: list = []):
    for reg in reg_op['map']:
        pprint_reg_op(reg, pre, out, prune_zero, no_prune)


def pprint_reg_op(reg: dict, pre: str = '', out: IO = sys.stdout, prune_zero: bool = False, no_prune: list = []):
    ppval = get_value_id(reg['val'])
    key: dict = reg['key']
    if not (prune_zero and ppval.startswith('0x0:') and key not in no_prune):
        match key:
            case {'arch_reg': name}:
                if name == '_PC' and ppval.startswith('0x0:'):
                    #  TODO: is this correct?
                    out.write(f'{pre}pc <- return address\n')
                elif name in {'_PC', 'PSTATE_C', 'PSTATE_V', 'PSTATE_N', 'PSTATE_Z'}:
                    out.write(f'{pre}{name} <- {ppval}\n')
            case {'reg': name}:
                out.write(f'{pre}{name} <- {ppval}\n')
            case {'hidden_reg': name}:
                # drop for now
                #out.write(f'{pre}Hidden Reg: {name}')
                pass
            case _:
                out.write(f'{pre}{key} <- {ppval}\n')


def pprint_memory_ops(memory_op: dict, pre: str = '', out: IO = sys.stdout, prune_zero: bool = False):
    if memory_op.get('mem_op'):
        pprint_mem_op(memory_op['mem_op'], pre, out, prune_zero)
    elif memory_op.get('external_call'):
        out.write(f'{pre}Event {memory_op["external_call"]}({",".join(map(pretty_call_arg, memory_op["args"]))})\n')
    else:
        out.write(f'{pre}Unknown mem op: {memory_op}')


def pprint_mem_op(mem_op: dict, pre: str = '', out: IO = sys.stdout, prune_zero: bool = False):
    out.write(f'{pre}{mem_op["direction"]} {get_value_id(mem_op["addr"])} ')
    match mem_op["direction"]:
        case 'Read':
            out.write('->')
        case 'Write':
            out.write('<-')
        case _:
            out.write('??')
    out.write(f' {get_value_id(mem_op["value"])}')
    #out.write(f' {mem_op["endianness"]}[{mem_op["size"]}]')
    if mem_op['condition'] != '"unconditional"':
        out.write(f' condition: {mem_op["condition"]}')
    out.write('\n')


def pretty_call_arg(arg):
    if isinstance(arg, dict) and 'data_expr' in arg:
        return str(arg['data_expr'])
    else:
        return str(arg)


def pprint_event_trace_instructions(events: dict, pre: str = '', out: IO = sys.stdout):
    """Pretty print an event trace's initial registers."""
    out.write(f'{pre}Instructions:\n')
    for e in events:
        ia = e['instruction_addr']
        if ia:
            out.write(f'{pre}  {get_addr_id(e["instruction_addr"])}\n')
            for op in e['events']:
                if op.get('memory_op'):
                    pprint_memory_ops(op['memory_op'], pre + '    ', out)
                elif op.get('register_op'):
                    pprint_reg_ops(op['register_op']['reg_op'], pre + '    ', out)


def pprint_node_inst_tree(inst_tree, pre: str = '', out: IO = sys.stdout):
    if not inst_tree:
        out.write(f'{pre}No instruction tree\n')
        return

    for i in inst_tree['prefix']:
        out.write(pre)
        out.write('S')
        out.write(str(i['address']['base']))
        out.write('+')
        out.write(i['address']['offset'])
        out.write('\n')
    # Dans says the branches in the tree are not necessarily the true and false arms of the branch. So we will just
    # label them A/B for now. We may be able to get T/F from binja since it does show this in its basic block graphs.
    if inst_tree['suffix_true']:
        pprint_node_inst_tree(inst_tree['suffix_true'], pre + 'A ', out)
    if inst_tree['suffix_false']:
        pprint_node_inst_tree(inst_tree['suffix_false'], pre + 'B ', out)


def tokenize_sexp(s: str):
    # Tokenize sexpression
    return filter(lambda x: re.match(r'\S', x),
                  re.split(r'(\(|\s+|\))', s))


def parse_sexp(tokens):
    try:
        t = next(tokens)
        if t == '(':
                items = []
                while True:
                    s = parse_sexp(tokens)
                    if s == ')':
                        return items
                    else:
                        items.append(s)
        elif t.isnumeric():
            return int(t)
        else:
            return t
    except StopIteration:
        return 'unexpected_end_of_sexp'


def assoc(x: Any, alist: list[list]) -> Any:
    """look up first x in the alist. Return None, if x not found."""
    for p in alist:
        if p[0] == x:
            return p[1]


def acons(k: Any, v: Any, alist: list[list]) -> list[list]:
    return [[k, v]] + alist


neg_op_map = {
    'bvslt': 'bvsge',
    'bvsle': 'bvsgt',
    'bvsgt': 'bvsle',
    'bvsge': 'bvslt',
    'intle': 'intgt',
    '=': '!=',
    '!=': '='
}

infix_op_map = {
    'bvmul': '*',
    'bvadd': '+',
    '=': '=',
    '!=': '!=',
    'bvslt': '<',
    'bvsle': '<=',
    'bvsgt': '>',
    'bvsge': '>=',
    'intlt': '<',
    'intle': '<=',
    'intgt': '>',
    'intge': '>=',
    'andp': '&',
    'orp': '|',
    'LTs' : '<',
    'LTu' : '<_u',
    'LEs' : '<=',
    'LEu' : '<=_u',
    'GTs' : '>',
    'GTu' : '>_u',
    'GEs' : '>=',
    'GEu' : '>=_u',
    'EQ' : '=',
    }


def simplify_sexp(sexp, env=None):
    if env is None:
        env = []
    if not isinstance(sexp, list) or len(sexp) == 0:
        return assoc(sexp, env) or sexp

    if sexp[0] == 'let':
        return simplify_sexp_let(sexp[1], sexp[2], env)

    # Normal expression
    op = sexp[0]
    arg = list(map(lambda x: simplify_sexp(x, env), sexp[1:]))

    # ('_', 'extract', s, e)(n) => n<s,e>
    if (isinstance(op, list) and len(op) == 4 and op[0] == '_' and op[1] == 'extract'
            and len(arg) == 1 and isinstance(arg[0], str)):
        return f'{arg[0]}<{op[2]}:{op[3]}>'

    # If op is not a string, don't try to process it.
    if not isinstance(op, str):
        return sexp

    # Simplify call(F, args...) => F(args...)
    if op == 'call' and len(arg) >= 1:
        return simplify_sexp([arg[0]] + arg[1:], env)

    # Simplify select(InitMemBytes, 0) => memory
    if op == 'select' and len(arg) == 2 and arg[0] == 'InitMemBytes' and arg[1] == 0:
        return 'memory'

    # Simplify select(memory, ADDR) => read1(ADDR)
    if op == 'select' and len(arg) == 2 and arg[0] == 'memory':
        return ['read1', arg[1]]

    # Simplify read{LE|GE}N(memory, ADDR) -> read{LE|GE}N(ADDR)
    if re.fullmatch(r'read(?:LE|GE)\d+', op) and len(arg) == 2 and arg[0] == 'memory':
        return [op, arg[1]]

    # Simplify sbvToInteger(x) => x
    if op == 'sbvToInteger' and len(arg) == 1:
        return arg[0]

    # Simplify multiply by 1
    if op == 'bvmul' and len(arg) == 2:
        if re.fullmatch(r'#x0*1', arg[0]):
            return arg[1]
        if re.fullmatch(r'#x0*1', arg[1]):
            return arg[0]

    # Simplify not(#b1) => False
    #          not(#b0) => True
    if op == 'notp' and len(arg) == 1:
        if arg[0] == '#b1':
            return False
        if arg[0] == '#b0':
            return True

    # Simplify (#b1 = x) => x
    if op == '=' and len(arg) == 2:
        if arg[0] == '#b1':
            return arg[1]
        if arg[1] == '#b1':
            return arg[0]

    # Simplify (#b1 != x) => not(x)
    if op == '!=' and len(arg) == 2:
        if arg[0] == '#b1':
            return simplify_sexp(['notp', arg[1]], env)
        if arg[1] == '#b1':
            return simplify_sexp(['notp', arg[0]], env)

    # Simplify (#b0 = x) => not(x)
    if op == '=' and len(arg) == 2:
        if arg[0] == '#b0':
            return simplify_sexp(['notp', arg[1]], env)
        if arg[1] == '#b0':
            return simplify_sexp(['notp', arg[0]], env)

    # Simplify (#b0 != x) => x
    if op == '!=' and len(arg) == 2:
        if arg[0] == '#b0':
            return arg[1]
        if arg[1] == '#b0':
            return arg[0]

    # Simplify (x and True) => x
    if op == 'andp' and len(arg) == 2:
        if arg[0] == True:
            return arg[1]
        if arg[1] == True:
            return arg[0]

    # Simplify (x or False) -> x
    if op == 'orp' and len(arg) == 2:
        if arg[0] == False:
            return arg[1]
        if arg[1] == False:
            return arg[0]

    # Simplify not(not x)) => x
    if op == 'notp' and len(arg) == 1:
        t = arg[0]
        if isinstance(t, list) and len(t) == 2 and t[0] == 'notp':
            return t[1]

    # Simplify (x = x) => True
    if op == '=' and len(arg) == 2:
        if arg[0] == arg[1]:
            return True

    # Simplify not(x & y) => (not(x) | not(y))
    if op == 'notp' and len(arg) == 1:
        t = arg[0]
        if isinstance(t, list) and len(t) == 3 and t[0] == 'andp':
            return ['orp',
                    simplify_sexp(['notp', t[1]], env),
                    simplify_sexp(['notp', t[2]], env)]

    # Simplify not(x | y) => (not(x) & not(y))
    if op == 'notp' and len(arg) == 1:
        t = arg[0]
        if isinstance(t, list) and len(t) == 3 and t[0] == 'orp':
            return ['andp',
                    simplify_sexp(['notp', t[1]], env),
                    simplify_sexp(['notp', t[2]],env)]

    # Simplify not(x op y) = (x nop y)
    if op == 'notp' and len(arg) == 1:
        x = arg[0]
        if isinstance(x, list) and len(x) == 3 and neg_op_map.get(x[0]):
            return [neg_op_map[x[0]], x[1], x[2]]

    # Simplify (ite c #b1 #b0) -> c
    if op == 'ite' and len(arg) == 3 and arg[1] == '#b1' and arg[2] == '#b0':
        return arg[0]

    # else
    return [op] + arg


def simplify_sexp_let(defs, body, env=None):
    if env is None:
        env = []
    for d in defs:
        x = simplify_sexp(d[1], env)
        env = acons(d[0], x, env)
    res = simplify_sexp(body, env)
    return res


def simple_sexp_to_str(sexp, isTop: bool = False):
    if not isinstance(sexp, list) or len(sexp) == 0:
        return str(sexp)

    if len(sexp) == 3 and infix_op_map.get(sexp[0]):
        x = simple_sexp_to_str(sexp[1])
        y = simple_sexp_to_str(sexp[2])
        result = f'{x} {infix_op_map[sexp[0]]} {y}'
        if not isTop:
            result = '(' + result + ')'
    else:
        result = str(sexp[0]) + "(" + ", ".join(map(simple_sexp_to_str, sexp[1:])) + ")"

    return result


def render_sexp(sexp, env=None):
    if env is None:
        env = []
    t = tokenize_sexp(sexp)
    s = parse_sexp(t)
    ss = simplify_sexp(s, env)
    return simple_sexp_to_str(ss, True)


def pprint_symbolic(out, v):
    if isinstance(v, dict) and v.get('symbolic'):
        env = list(map(lambda x: x[::-1], v['vars']))
        fenv = list(map(lambda x: x[::-1], v['fns']))
        # TODO: Pending question to Dan about variable and function namespaces. Do I need to keep them independent?
        env = env + fenv
        s = render_sexp(v.get('symbolic'), env)
        out.write(s)

        # pprint.PrettyPrinter(indent=4, stream=out).pprint(s)
        # out.write('\n      ')
        # out.write(re.sub('\s+', ' ', v['symbolic']))
        # if v.get('vars'):
        #     out.write(f'\n      env: {env}')
        #     out.write(f'\n      vars: {v["vars"]}')
        # if v.get('fns'):
        #     out.write(f'\n      fenv: {fenv}\n')
        #     out.write(f'\n      fns: {v["fns"]}')

    else:
        out.write(str(v))


def pprint_val_domain(v, pre: str = '', out: IO = sys.stdout):
    if v != 'TODO':
        out.write(f'{pre}Value: {v}/n')


class TtyUserInteraction(PateUserInteraction):
    ask_show_cfar_graph: bool

    def __init__(self, ask_show_cfar_graph: bool = False):
        self.ask_show_cfar_graph = ask_show_cfar_graph

    def ask_user(self, prompt: str, choices: list[str], replay_choice: Optional[str] = None) -> str:
        print()
        print(prompt)
        for i, e in enumerate(choices):
            print('  {}'.format(e))

        if replay_choice:
            # In replay mode, response is ignored, just return anything for fast replay
            choice = replay_choice
            print(f'Pate command (replay): {choice}\n')
        else:
            choice = input("Pate command: ")

        return choice

    def show_message(self, msg: str) -> None:
        print(msg)

    def show_cfar_graph(self, graph: CFARGraph) -> None:
        if self.ask_show_cfar_graph:
            print()
            choice = input("Show CFAR Graph (y or n)? ")
        else:
            # Choose which you want when no ask
            #choice = 'y'
            choice = 'n'

        if choice == 'y':
            print('\nPate CFAR Graph:\n')
            graph.pprint()

        focusNodes = graph.getFocusNodes()
        print('Focus Nodes:')
        for n in focusNodes:
            print(f'   {n.id}')


def load_run_config(file: os.PathLike) -> Optional[dict]:
    try:
        with open(file, 'r') as f:
            config = json.load(f)
        return config
    except OSError:
        return None


def get_demo_files():
    files = []
    demoDir = pathlib.Path(os.getenv('PATE_BINJA_DEMOS'))
    included_extensions = ['run-config.json', 'replay']
    allFiles = demoDir.rglob('*')
    files = [str(fn) for fn in allFiles
                  if any(fn.name.endswith(ext) for ext in included_extensions)]
    return files


def run_pate_demo():
    files = get_demo_files()
    print("Select PATE run configuration or replay file:")
    for i, f in enumerate(files):
        print('  {}: {}'.format(i, f))
    choice = input("Choice: ")
    file = files[int(choice)]

    replay = file.endswith('.replay')
    user = TtyUserInteraction(False) # Don't prompt to show CFAR graph for now
    #user = TtyUserInteraction(not replay)
    pate = PateWrapper(file, user)
    #pate.debug_cfar = True
    pate.run()


