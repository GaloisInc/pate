# Copyright 2023-2024, Galois Inc. All rights reserved.

from __future__ import annotations

import abc
import io
import json
import os
import pprint
import re
import shlex
import sys
import warnings
from json import JSONDecodeError
from subprocess import Popen, PIPE, STDOUT
from typing import IO, Any, Optional

# TODO: Get rid of these globals
pp = pprint.PrettyPrinter(indent=4)


class PateUserInteraction(abc.ABC):
    @abc.abstractmethod
    def ask_user(self, prompt: str, choices: list[str]) -> Optional[str]:
        pass

    @abc.abstractmethod
    def show_message(self, msg) -> None:
        pass

    @abc.abstractmethod
    def show_cfar_graph(self, graph: CFARGraph) -> None:
        pass


class PateWrapper:
    def __init__(self, user: PateUserInteraction, pate_out: IO, pate_in: IO, trace: IO = None):
        self.debug_io = False
        self.debug_json = False
        self.debug_cfar = False
        self.user = user
        self.pate_in = pate_in
        self.pate_out = pate_out
        self.trace_file = trace

    def next_line(self) -> str:
        line = self.pate_out.readline()
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
                    self.command('goto_prompt')
                    # Skip lines till we get json
                    gotoPromptAfterNonJson = False
            else:
                return rec

    def skip_lines_till(self, s: str) -> None:
        """Skip lines till EOF or line completely matching s (without newline)."""
        while True:
            line = self.next_line().rstrip('\n')
            self.user.show_message(line)
            if line == s:
                break

    def command(self, cmd: str) -> None:
        if self.pate_in:
            if self.debug_io:
                print('Command to Pate: ', cmd)
            print(cmd, file=self.pate_in, flush=True)

    def extract_graph(self) -> CFARGraph:
        cfar_graph = CFARGraph()

        self.command('top')
        top = self.next_json()

        self.extract_graph_rec(top, [], None, cfar_graph, None, None)

        self .connect_divergence_nodes(cfar_graph)
        self .connect_synchronization_nodes(cfar_graph)

        self.prune_orphans(cfar_graph)

        return cfar_graph

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
            # Prune non-matching exits from divergedAt node and splice around remaining parts
            parts = [e for e in n.exits if e.id.startswith(n.id)]
            n.exits = []
            for p in parts:
                for e in p.exits:
                    n.addExit(e)
                p.exits = []

            if self.debug_cfar:
                print('CFAR ID (divergedAt):', n.id)
                print("Remaining exits:")
                for e in n.exits:
                    print('   ', e.id)

    def prune_orphans(self, graph: CFARGraph):
        while True:
            orphans = []
            for n in graph.nodes.values():
                if not n.id.startswith('Function entry ') and not graph.get_parents(n):
                    # Found an orphan
                    orphans.append(n)
            for n in orphans:
                # TODO: move this to a delete method
                if self.debug_cfar:
                    print('CFAR prune: ', n.id)
                n.exits = []
                del graph.nodes[n.id]
            if not orphans:
                # Done
                break

    def connect_synchronization_nodes_OLD(self, graph: CFARGraph):
        # TODO: Replace string hacks with something more resilient.
        for n in list(graph.nodes.values()):
            if (n.id.find(' vs ') >= 0
                    and isinstance(n.data, dict)
                    and n.data.get('trace_node_kind') == 'node'
                    and not graph.get_parents(n)):
                if self.debug_cfar:
                    print()
                    pp.pprint(n.data)
                    print('CFAR Synchronization node:', n.id)
                parts = n.id.split(' vs ')
                if len(parts) != 2:
                    print('WARNING: Did not get exactly two parts for CFAR synchronization node. Skipping:', id)
                else:
                    o_id = parts[0] +  ' (original)'
                    o_node = graph.get(o_id)
                    if o_node:
                        # splice around o_node
                        for p in graph.get_parents(o_node):
                            p.exits.remove(o_node)
                            p.addExit(n)
                        # delete o_node
                        o_node.exits = []
                        del graph.nodes[o_node.id]

                    p_id = parts[1] +  ' (patched)'
                    p_node = graph.get(p_id)
                    if p_node:
                        # splice around p_node
                        for p in graph.get_parents(p_node):
                            p.exits.remove(p_node)
                            p.addExit(n)
                        # delete p_node
                        p_node.exits = []
                        del graph.nodes[p_node.id]

    def connect_synchronization_nodes(self, graph: CFARGraph):
        # TODO: Replace string hacks with something more resilient.
        for n in list(graph.nodes.values()):

            if n.id == 'S1+0x1a98 in S1+0x18e4(RR_ReadTlmInput)':
                pass

            if (True #not graph.get_parents(n)
                    and isinstance(n.data, dict)
                    and n.data.get('trace_node_kind') == 'node'):

                if (n.data['trace_node'].get('graph_node_type') == 'entry'
                        and n.data['trace_node']['entry_body']['blocks'].get('original')
                        and n.data['trace_node']['entry_body']['blocks'].get('patched')):
                    o_rec = n.data['trace_node']['entry_body']['blocks']['original']
                    o_id = get_ref_id(o_rec) + ' (original)'
                    p_rec = n.data['trace_node']['entry_body']['blocks']['patched']
                    p_id = get_ref_id(p_rec) + ' (patched)'
                else:
                    continue

                if self.debug_cfar:
                    print()
                    #pp.pprint(n.data)
                    print('CFAR Synchronization node:', n.id)

                o_node = graph.get(o_id)
                if o_node:
                    # splice around o_node
                    if self.debug_cfar:
                        print('  Replacing original node:', o_node.id)
                    for p in graph.get_parents(o_node):
                        p.exits.remove(o_node)
                        p.addExit(n)
                    # delete o_node
                    o_node.exits = []
                    del graph.nodes[o_node.id]

                p_node = graph.get(p_id)
                if p_node:
                    # splice around p_node
                    if self.debug_cfar:
                        print('  Replacing patched node:', p_node.id)
                    for p in graph.get_parents(p_node):
                        p.exits.remove(p_node)
                        p.addExit(n)
                    # delete p_node
                    p_node.exits = []
                    del graph.nodes[p_node.id]

    def extract_graph_rec(self,
                          rec: dict,
                          path: list[int],
                          context: dict | None,
                          cfar_graph: CFARGraph,
                          cfar_parent: CFARNode | None,
                          cfar_exit: CFARNode | None
                          ) -> None:
        this = rec.get('this')
        this = this.replace('\n',' ')
        trace_node = rec.get('trace_node')

        if self.debug_cfar:
            print('\nJSON {}:'.format(path))
            pp.pprint(rec)

        # Hack to find counter-example trace. Really need to restructure this whole method.
        if (len(path) == 4
            and len(rec.get('trace_node_contents', [])) >= 3
            and rec['trace_node_contents'][1].get('pretty') == 'Equivalence Counter-example'
            ):
            for c in rec['trace_node_contents']:
                if c.get('content', {}).get('traces', {}):
                    cfar_parent.addExitMetaData(cfar_exit, 'ce_event_trace', c['content'])
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

        elif rec['trace_node_kind'] == 'blocktarget':
            id = get_blocktarget_id(rec, context, cfar_parent)
            existing_cfar_node = cfar_graph.get(id)
            cfar_node = cfar_graph.add_node(id, this, rec)

        # If we created a CFAR node and have a parent, link them up.
        if cfar_node and cfar_parent:
            cfar_exit = cfar_node
            cfar_parent.addExit(cfar_node)
            if rec['trace_node_kind'] == 'blocktarget':
                for c in  rec['trace_node_contents']:
                    if c.get('content') and c['content'].get('traces', {}):
                        cfar_parent.addExitMetaData(cfar_exit, 'event_trace', c['content'])
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
            if exit_id == 'None' or exit_id.startswith('return_target'):
                pass
            else:
                exit_node = cfar_graph.add_node(exit_id, 'junk', {})
                cfar_node.addExit(exit_node)
                if self.debug_cfar:
                    print('CFAR ID (exit):', exit_id)

        for i, child in enumerate(rec['trace_node_contents']):
            child = child['content']
            if not child:
                continue
            # TODO: Ask Dan about this filter.
            if ((len(path) == 0 and child.get('trace_node_kind') in {'node'})
                    or (len(path) == 1 and child.get('subtree_kind') == '"blocktarget"')
                    or (len(path) == 2 and child.get('trace_node_kind') in {'blocktarget'})
                    # Look for counter-example trace
                    or (len(path) == 3 and rec.get('trace_node_kind') == 'blocktarget'
                        and child.get('trace_node_kind') == 'node')):
                self.command(str(i))
                childrec = self.next_json()
                # update with values from child. TODO: ask Dan about this?
                childrec.update(child)
                self.extract_graph_rec(childrec, path + [i], context, cfar_graph, cfar_parent, cfar_exit)
                self.command('up')
                # Consume result of up, but do not need it
                ignore = self.next_json()
            # else:
            #     if self.debug_cfar:
            #         print('CFAR skip child:')
            #         pp.pprint(child)

    def _ask_user(self, prompt_rec: dict) -> str:
        # Read entry point choices
        prompt = prompt_rec['this']
        choices = list(map(get_choice_id, prompt_rec.get('trace_node_contents', [])))
        while True:
            choice = self.user.ask_user(prompt, choices).strip()
            if choice:
                return choice
            self.user.show_message("error: empty choice")


    def command_loop(self):
        rec = self.next_json()
        self.command('goto_prompt')
        while self.command_step():
            pass
        self.user.show_message("Pate finished")

    def command_step(self):
        # Process one json record from pate
        try:
            rec = self.next_json(gotoPromptAfterNonJson=True)
            return self.process_json(rec)
        except EOFError:
            self.user.show_message("Pate terminated unexpectedly")
            return False

    def process_json(self, rec):

        if self.debug_json:
            print('\nProcessing JSON:')
            pp.pprint(rec)

        if (isinstance(rec, dict) and rec.get('this')
                and rec.get('trace_node_contents') is not None
                and rec['this'].startswith('Assumed Equivalence Conditions')):
            # pprint the eq cond
            eqCond = rec['trace_node_contents'][len(rec['trace_node_contents']) - 1]['content'].get('trace_node')
            if eqCond:
                self.user.show_message('\n\nFinal Equivalence Condition:')
                self.user.show_message(eqCond.replace('\\n', '\n') + '\n')
                return False

            eqCond = rec['trace_node_contents'][len(rec['trace_node_contents']) - 1]['content'].get('extra_preds')
            if eqCond:
                self.user.show_message('\n\nFinal Equivalence Condition:')
                with io.StringIO() as out:
                    for p in eqCond['predicates']:
                        out.write('  ')
                        pprint_symbolic(out, p)
                        out.write('\n')
                    self.user.show_message(out.getvalue())
                return False

        elif isinstance(rec, dict) and rec.get('this') and rec.get('trace_node_contents'):
            # Prompt User
            # TODO: Heuristic for when to update graph. Ask Dan. Maybe add flag to JSON?
            if rec['this'].startswith('Control flow desynchronization found at') \
                    or rec['this'].startswith('Continue verification?'):
                # Extract flow graph
                cfar_graph = self.extract_graph()
                if cfar_graph:
                    self.user.show_cfar_graph(cfar_graph)
                # Go back to prompt
                self.command('goto_prompt')
                rec = self.next_json()
            choice = self._ask_user(rec)
            self.command(choice)

        elif isinstance(rec, list) and rec[len(rec) - 1]['content'] == {'node_kind': 'final_result'}:
            # TODO: Hack to detect finish. Talk to Dan about providing a better mechanism.
            choices = list(map(get_choice_id, rec))
            choice = self.user.ask_user('Final Prompt:', choices)
            self.command(choice)

        elif isinstance(rec, dict) and rec.get('trace_node_kind') == 'equivalence_result':
            # Done if we got an equivalence result
            self.user.show_message(rec['this'] + '\n')
            return False

        elif isinstance(rec, dict) and rec.get('error'):
            self.show_message('error: ' + rec['error'])
            self.command('goto_prompt')

        else:
            # Message(s)
            self.show_message(rec)

        return True

    def show_message(self, rec: Any):

        if isinstance(rec, list):
            for m in rec:
                self.user.show_message("Processing ... " + get_choice_id(m))
        elif isinstance(rec, dict) and rec.get('message'):
            self.user.show_message(rec['message'])
        else:
            self.user.show_message(str(rec))


class CFARNode:
    exits: list[CFARNode]

    def __init__(self, id: str, desc: str, data: dict):
        self.id = id
        self.exits = []
        self.exit_meta_data = {}
        self.update_node(desc, data)
        self.desc = desc
        self.data = data
        self.predomain = None
        self.postdomain = None
        self.external_postdomain = None
        self.addr = None

    def update_node(self, desc: str, data: dict):
        self.desc = desc
        self.data = data
        self.predomain = get_domain(data, 'Predomain')
        self.postdomain = get_domain(data, 'Postdomain')
        self.external_postdomain = get_domain(data, 'ExternalPostDomain')

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
            warnings.warn('Meta data already exists. Overwriting.')
        # Add the meta data
        self.exit_meta_data[exit][key] = val

    def isExit(self, node: CFARNode) -> bool:
        return node in self.exits

    def pprint(self, pre: str = ''):
        print(f'{pre}CFAR Node: {self.id}')
        print(f'{pre}desc: {self.desc}')
        self.pprint_node_contents(pre)
        print()
        #print('data:')
        #pp.pprint(self.data)

    def pprint_node_contents(self, pre: str = '', out: IO = sys.stdout, show_ce_trace: bool = False):
        self.pprint_node_domain(pre, out, show_ce_trace)
        if show_ce_trace:
            for n in self.exits:
                out.write(f'{pre}Exit: {n.id}\n')
                if self.exit_meta_data.get(n,{}).get('ce_event_trace'):
                    self.pprint_node_event_trace(self.exit_meta_data[n]['ce_event_trace'], 'Counter-Example', pre + '  ', out)
                elif self.exit_meta_data.get(n, {}).get('event_trace'):
                     self.pprint_node_event_trace(self.exit_meta_data[n]['event_trace'], '', pre + '  ', out)

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

    def pprint_node_event_trace(self, trace, label: str, pre: str = '', out: IO = sys.stdout):
        self.pprint_node_event_trace_domain(trace, label, pre, out)
        self.pprint_node_event_trace_original(trace, label, pre, out)
        self.pprint_node_event_trace_patched(trace, label, pre, out)

    def pprint_node_event_trace_domain(self, trace, label: str, pre: str = '', out: IO = sys.stdout):
        if trace.get('precondition'):
            out.write(f'{pre}Precondition:\n')
            pprint_eq_domain(trace['precondition'], pre + '  ', out)
        if trace.get('postcondition'):
            out.write(f'{pre}Postcondition:\n')
            pprint_eq_domain(trace['postcondition'], pre + '  ', out)

    def pprint_node_event_trace_original(self, trace, label: str, pre: str = '', out: IO = sys.stdout):
        if trace.get('traces', {}).get('original'):
            pprint_event_trace(f'{label} Original', trace['traces']['original'], pre, out)

    def pprint_node_event_trace_patched(self, trace, label: str, pre: str = '', out: IO = sys.stdout):
        if trace.get('traces',{}).get('patched'):
            pprint_event_trace(f'{label} Patched', trace['traces']['patched'], pre, out)

class CFARGraph:
    nodes: dict[str, CFARNode]

    def __init__(self):
        self.nodes = {}

    def get(self, id):
        return self.nodes.get(id)

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
        for n in self.nodes.values():
            n.pprint()


    def get_parents(self, node: CFARNode) -> list[CFARNode]:
        parents = []
        for n in self.nodes.values():
            for e in n.exits:
                if node == e:
                    parents.append(n)
        return parents


def get_addr_id(a: dict):
    base = a['base']
    offset = a['offset']
    if base == 0:
        return offset
    else:
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
    # 'finished' only relevant when checking asynchronously. If it's false it means that the node is still under
    # construction.
    finished = rec['finished']
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
                pass
            case 'stack_base':
                # TODO: Ask Dan about these. They appear in trace pre/post conditions
                pass
            case _:
                out.write(f'{pre}Unknown eq domain "{k}": {v}\n')


def pprint_eq_domain_registers(v, pre: str = '', out: IO = sys.stdout):
    for m in v['map']:
        if m.get('pred') == True:
            # TODO: does this apply to pre/post domains and trace conditions?
            continue
        if m['val'] != True:
            match m['key']:
                case {'arch_reg': name}:
                    if name in {'PSTATE_C', 'PSTATE_V', 'PSTATE_N', 'PSTATE_Z'}:
                        out.write(f'{pre}Register: {name}\n')
                    else:
                        continue
                case {'reg': name}:
                    out.write(f'{pre}Register: {name}\n')
                case _:
                    out.write(f'{pre}{m["key"]}\n')
            if m['val'] != False:
                out.write(f'{pre}val: {m["val"]}')


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
            if region == 0 or (region == 1 and mem_kind =='Stack Slot'):
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


def pprint_event_trace(k: str, et: dict, pre: str = '', out: IO = sys.stdout):
    # TODO: Dropping this for now. Unclear how useful this is to an end user without filtering.
    #pprint_event_trace_initial_reg(k, et['initial_regs'], pre, out)
    pprint_event_trace_events(k, et['events'], pre, out)


def pprint_event_trace_initial_reg(k: str, initial_regs: dict, pre: str = '', out: IO = sys.stdout):
    """Pretty print an event trace's initial registers."""
    out.write(f'{pre}{k} Initial Register Values (non-zero):\n')
    pprint_reg_op(initial_regs['reg_op'], pre + '  ', out, True)


def pprint_reg_op(reg_op: dict, pre: str = '', out: IO = sys.stdout, prune_zero: bool = False):
    for r in reg_op['map']:
        val: dict = r['val']
        ppval = get_value_id(val)
        key: dict = r['key']
        if (not isinstance(val, dict)
                or not prune_zero
                or not ppval.startswith('0x0:')):
            match key:
                case {'arch_reg': name}:
                    if name == '_PC' and ppval.startswith('0x0:'):
                        #  TODO: is this correct?
                        out.write(f'{pre}pc <- return address\n')
                    elif name in {'PSTATE_C', 'PSTATE_V', 'PSTATE_N', 'PSTATE_Z'}:
                        out.write(f'{pre}{name} <- {ppval}\n')
                case {'reg': name}:
                    out.write(f'{pre}{name} <- {ppval}\n')
                case {'hidden_reg': name}:
                    # drop for now
                    #out.write(f'{pre}Hidden Reg: {name}')
                    pass
                case _:
                    out.write(f'{pre}{key} <- {ppval}\n')


def pprint_mem_op(mem_op: dict, pre: str = '', out: IO = sys.stdout, prune_zero: bool = False):
    if mem_op.get('mem_op'):
        mem_op = mem_op['mem_op']
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
    elif mem_op.get('external_call'):
        out.write(f'{pre}{mem_op["external_call"]}({",".join(mem_op["args"])})\n')
    else:
        out.write(f'{pre}Unknown mem op: {mem_op}')


def pprint_event_trace_events(k: str, events: dict, pre: str = '', out: IO = sys.stdout):
    """Pretty print an event trace's initial registers."""
    out.write(f'{pre}{k} Instructions:\n')
    for e in events:
        ia = e['instruction_addr']
        if ia:
            out.write(f'{pre}  {get_addr_id(e["instruction_addr"])}\n')
            for op in e['events']:
                if op.get('memory_op'):
                    pprint_mem_op(op['memory_op'], pre + '    ', out)
                elif op.get('register_op'):
                    pprint_reg_op(op['register_op']['reg_op'], pre + '    ', out)


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
    'andp': '&',
    'orp': '|'
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

    # Simplify multiply by 1
    if op == 'bvmul' and len(arg) == 2:
        if arg[0] == '#x00000001':
            return arg[1]
        if arg[1] == '#x00000001':
            return arg[0]

    # Simplify (#b1 = x) => x
    if op == '=' and len(arg) == 2:
        if arg[0] == '#b1':
            return simplify_sexp(arg[1], env)

    # Simplify and
    if op == 'andp' and len(arg) == 2:
        if arg[0] == True:
            return arg[1]
        if arg[1] == True:
            return arg[0]

    # Simplify or
    if op == 'orp' and len(arg) == 2:
        if arg[0] == False:
            return arg[1]
        if arg[1] == False:
            return arg[0]

    # Simplify x = x
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
                    simplify_sexp(['notp', t[2]], env)]

    # Simplify not(x op y)
    if op == 'notp' and len(arg) == 1:
        x = arg[0]
        if isinstance(x, list) and len(x) == 3 and neg_op_map.get(x[0]):
            return [neg_op_map[x[0]], x[1], x[2]]

    # Simplify (ite c #b1 #b0) -> c
    if op == 'ite' and len(arg) == 3 and arg[1] == '#b1' and arg[2] == '#b0':
        return simplify_sexp(arg[0], env)

    # else
    return [op] + list(map(lambda x: simplify_sexp(x, env), sexp[1:]))


def simplify_sexp_let(defs, body, env=None):
    if env is None:
        env = []
    for d in defs:
        x = simplify_sexp(d[1], env)
        env = acons(d[0], x, env)
    return simplify_sexp(body, env)


def simple_sexp_to_str(sexp):
    if not isinstance(sexp, list) or len(sexp) == 0:
        return str(sexp)

    if len(sexp) == 3 and infix_op_map.get(sexp[0]):
        x = simple_sexp_to_str(sexp[1])
        y = simple_sexp_to_str(sexp[2])
        return f'({x} {infix_op_map[sexp[0]]} {y})'

    # else
    return str(sexp[0]) + "(" + ", ".join(map(simple_sexp_to_str, sexp[1:])) + ")"


def render_sexp(sexp, env=None):
    if env is None:
        env = []
    t = tokenize_sexp(sexp)
    s = parse_sexp(t)
    ss = simplify_sexp(s, env)
    return simple_sexp_to_str(ss)


def pprint_symbolic(out, v):
    if isinstance(v, dict) and v.get('symbolic'):
        env = list(map(lambda x: x[::-1], v['vars']))
        s = render_sexp(v.get('symbolic'), env)
        out.write(s)

        # out.write('\n      ')
        # out.write(re.sub('\s+', ' ', v['symbolic']))
        # if v.get('vars'):
        #     out.write(f'\n      vars: {v["vars"]}')
        # if v.get('fns'):
        #     out.write(f'\n      vars: {v["fns"]}')

    else:
        out.write(str(v))


def pprint_val_domain(v, pre: str = '', out: IO = sys.stdout):
    if v != 'TODO':
        out.write(f'{pre}Value: {v}/n')


class TtyUserInteraction(PateUserInteraction):
    def __init__(self, replay: bool = False):
        self.replay = replay

    def ask_user(self, prompt: str, choices: list[str]) -> str:
        print()
        print(prompt)
        for i, e in enumerate(choices):
            print('  {}'.format(e))

        # # Hack to auto respond for nov23 target 3. Need more cases.
        # if prompt == 'Control flow desynchronization found at: GraphNode segment1+0x1ad0 [ via: "RR_ReadTlmInput" (segment1+0x18e4) ]':
        #     print('Pate command: 3\n')
        #     return 3

        if self.replay:
            # In replay mode, response is ignored, just return anything for fast replay
            print('Pate command: auto replay\n')
            choice = 42
        else:
            choice = input("Pate command: ")
        return choice

    def show_message(self, msg: str) -> None:
        print(msg)

    def show_cfar_graph(self, graph: CFARGraph) -> None:
        print()
        if self.replay:
            # In replay mode, just return true for fast replay
            choice = 'y'  # For fast replay
        else:
            choice = input("Show CFAR Graph (y or n)? ")
        if choice == 'y':
            print('\nPate CFAR Graph:\n')
            graph.pprint()


def test(pate_out, pate_in, trace):
    user = TtyUserInteraction(pate_in is None)
    pate = PateWrapper(user, pate_out, pate_in, trace)

    #pate.debug_io = True
    #pate.debug_cfar = True

    pate.command_loop()


def test_live(run_fn):
    with open("trace.txt", "w") as trace:
        with run_fn(False) as proc:
            test(proc.stdout, proc.stdin, trace)


def test_replay(run_fn):
    with run_fn(True) as proc:
        test(proc.stdout, proc.stdin, None)


def run_replay(file: str) -> Popen:
    return Popen(
        ['cat', file],
        stdin=None, stdout=PIPE, text=True, encoding='utf-8'
        )


def get_run_config(file: os.PathLike) -> dict:
    with open(file, 'r') as f:
        config = json.load(f)
    config['cwd'] = os.path.dirname(file)
    return config


def run_config(config: dict):
    cwd = config.get('cwd')
    original = config.get('original')
    patched = config.get('patched')
    rawargs = config.get('args')
    args = shlex.split(' '.join(rawargs))
    # TODO: Error checking
    return run_pate(cwd, original, patched, args)


def run_pate(cwd: str, original: str, patched: str, args: list[str]) -> Popen:
    # We use a helper script to run logic in the user's shell environment.
    script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "run-pate.sh")
    # Need -l to make sure user's env is fully setup (e.g. access to docker and ghc tools).
    return Popen(['/bin/bash', '-l', script, '-o', original, '-p', patched, '--json-toplevel'] + args,
                 cwd=cwd,
                 stdin=PIPE, stdout=PIPE,
                 stderr=STDOUT,
                 text=True, encoding='utf-8',
                 close_fds=True,
                 # Create a new process group, so we can kill it cleanly
                 preexec_fn=os.setsid
                 )


def run_pate_config_or_replay_file(f: str) -> Popen:
    if f.endswith(".run-config.json"):
        config = get_run_config(f)
        test_live(lambda ignore: run_config(config))
    elif f.endswith(".replay"):
        test_replay(lambda ignore: run_replay(f))


def get_demo_files():
    files = []
    demos_dir = os.getenv('PATE_BINJA_DEMOS')
    if demos_dir:
        # TODO: Search dir for matching files rather than hardcoded list
        for d in ['may23-challenge10', 'nov23-target1-room1018', 'nov23-target4-room1011-dendy']:
            for ext in ['.run-config.json', '.replay']:
                f = os.path.join(demos_dir, d, d + ext)
                if os.path.isfile(f):
                    files.append(f)
    return files

def run_pate_demo():
    files = get_demo_files()
    print("Select PATE run configuration or replay file:")
    for i, f in enumerate(files):
        print('  {}: {}'.format(i, f))

    choice = input("Choice: ")
    file = files[int(choice)]
    run_pate_config_or_replay_file(file)
