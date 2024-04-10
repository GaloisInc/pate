from typing import Optional

import grpc
from binaryninja import BinaryView

from . import binja_pb2_grpc, binja_pb2
from .. import view

class PateMcad:
    def __init__(self):
        self.channel = grpc.insecure_channel("localhost:50052")
        self.stub = binja_pb2_grpc.BinjaStub(self.channel)

    def request_cycle_counts(self, instructions: binja_pb2.BinjaInstructions):
        return self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=instructions))

    def annotate_inst_tree(self, inst_tree: Optional[dict], bv: BinaryView):
        """Add MCAD cycle counts to instruction tree. NOOP if cycle counts all ready exist."""
        if not inst_tree:
            return

        # Get the list of instruction bytes for the block
        instructions = []
        for instAddr in inst_tree['prefix']:
            if instAddr.get('cycleCount'):
                # We already got the cycle counts for this instruction tree.
                return
            # TODO: Ignore base for now. Ask Dan about this.
            # base = int(instAddr['address']['base'], 16?)
            offset = int(instAddr['address']['offset'], 16)
            arch = view.getInstArch(offset, bv)
            instLen = bv.get_instruction_length(offset, arch)
            instBytes = bv.read(offset, instLen)
            instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=instBytes))

        if instructions:
            # Get the cycle counts from MCAD
            cycleCounts = self.request_cycle_counts(instructions)

            # Annotate the instruction tree with cycle counts
            for (instAddr, cycleCount) in zip(inst_tree['prefix'], cycleCounts.cycle_count):
                instAddr['cycleCount'] = cycleCount

        # Process the children. Note: true/false are not necessarily accurate.
        self.annotate_inst_tree(inst_tree['suffix_true'], bv)
        self.annotate_inst_tree(inst_tree['suffix_false'], bv)

    def getInstTreeLines(self, instTree, bv, pre: str='', cumu: int=0):

        if not instTree:
            return []

        prefixLines = []
        for instAddr in instTree['prefix']:
            line = ''
            if instAddr.get('cycleCount'):
                cc: binja_pb2.CycleCounts.CycleCount = instAddr['cycleCount']
                cycles = cc.executed - cc.ready
                cumu += cycles
                line += f'{cycles:2d}'
                if cc.is_under_pressure:
                    line += '!'
                else:
                    line += ' '
                line += f' {cumu:4d}'
            else:
                line += ' ' * 8

            # TODO: Ignore base for now. Ask Dan about this.
            # base = int(instAddr['address']['base'], 16?)
            offset = int(instAddr['address']['offset'], 16)
            arch = view.getInstArch(offset, bv)
            disassembly = next(bv.disassembly_text(offset, arch),['??????'])[0]
            line += f' {pre}{offset:08x} {disassembly}'

            prefixLines.append(line)

        # Process the children. Note: true/false are not necessarily accurate.
        trueBranchLines = self.getInstTreeLines(instTree['suffix_true'], bv, pre + '+', cumu)
        falseBranchLines = self.getInstTreeLines(instTree['suffix_false'], bv, pre + '-', cumu)

        return prefixLines + trueBranchLines + falseBranchLines






