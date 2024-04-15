import os
import shutil
import signal
import subprocess
import sys
import threading
import time
from typing import Optional, IO

import grpc
from binaryninja import BinaryView, Architecture

from . import binja_pb2_grpc, binja_pb2
from .. import view

class PateMcad:
    def __init__(self, arch: Architecture):
        self.arch = arch
        self.proc = None
        self.channel = None
        self.stub = None

    def isRunning(self) -> bool:
        return bool(self.proc)

    def start(self):
        if self.proc:
            # MCAD server already started.
            return

        port = 50052
        dockerName = 'mcad-dev'
        mtriple, mcpu = self._get_triple_and_cpu()
        # TODO: This is dependent on arch of docker image (eg apple silicon vs x86_64)
        brokerPluginPath = '/work/LLVM-MCA-Daemon/build/plugins/binja-broker/libMCADBinjaBroker.so'

        args = ['/usr/local/bin/docker',  # TODO: Path is os specific
                'run',
                '-p', f'{port}:50052',
                dockerName,
                # TODO: Do I really want debug?
                #'--debug',
                f'-mtriple={mtriple}',
                f'-mcpu={mcpu}',
                # TODO: Ask about these three
                #'--use-call-inst',
                #'--use-return-inst',
                #'--noalias=false',
                f'-load-broker-plugin={brokerPluginPath}',
                ]
        #args = ['/bin/echo', 'FNORT']
        self.proc = subprocess.Popen(args,
                                     # Create a new process group, so we can kill it cleanly
                                     preexec_fn=os.setsid,
                                     text=True, encoding='utf-8',
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT,
                                     )
        print('docker started: ', self.proc)
        #print('Blahhh: ', self.proc.communicate(5))
        t = threading.Thread(target=_echoLines, args=[f'MCAD {self.arch}:', self.proc.stdout], daemon=True)
        t.start()
        time.sleep(1)
        self.channel = grpc.insecure_channel(f"localhost:{port}")
        self.stub = binja_pb2_grpc.BinjaStub(self.channel)

    def stop(self) -> None:
        if self.proc:
            # Asking for cycle counts with empty instruction list should cause server to exit
            print('STOPPING MCAD Process', self.proc)
            self.request_cycle_counts([])
            try:
                self.pate_proc.wait(2)
            except subprocess.TimeoutExpired:
                # Orderly shutdown did not work, kill the process group
                print('KILLING MCAD Process', self.proc)
                os.killpg(self.proc.pid, signal.SIGKILL)
            self.proc = None

    def _get_triple_and_cpu(self):
        if self.arch.name == "x86_64":
            return "x86_64-unknown-linux-gnu", "skylake"

        elif self.arch.name == "armv7":
            return "armv7-linux-gnueabih", "cortex-a57"

        elif self.arch.name == "thumb2":
            return "thumbv8", "cortex-a57"

        elif self.arch.name == "aarch64":
            return "aarch64-unknown-linux-gnu", "cortex-a55"

        else:
            return None

    def request_cycle_counts(self, instructions: binja_pb2.BinjaInstructions) -> Optional[binja_pb2.CycleCounts.CycleCount]:
        if not self.isRunning:
            return None

        return self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=instructions))

    def annotate_inst_tree(self, inst_tree: Optional[dict], bv: BinaryView):
        if not self.isRunning:
            return

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
            # TODO: Check for gRPC error
            cycleCounts: binja_pb2.CycleCounts.CycleCount = self.request_cycle_counts(instructions)

            if cycleCounts:
                # Annotate the instruction tree with cycle counts
                for (instAddr, cycleCount) in zip(inst_tree['prefix'], cycleCounts.cycle_count):
                    instAddr['cycleCount'] = cycleCount

        # Process the children. Note: true/false are not necessarily accurate.
        self.annotate_inst_tree(inst_tree['suffix_true'], bv)
        self.annotate_inst_tree(inst_tree['suffix_false'], bv)

def _echoLines(pre: str, io: IO):
    for line in io:
        print(pre, line)








