from __future__ import annotations

import os
import signal
import subprocess
import threading
import time
from typing import Optional, IO, List

import grpc

from . import binja_pb2_grpc, binja_pb2

class CycleCount:
    def __init__(self, ready: int, executed: int, is_under_pressure: bool):
        self.ready = ready
        self.executed = executed
        self.is_under_pressure = is_under_pressure

    def __repr__(self):
        return f'CycleCount({self.ready}, {self.executed}, {self.is_under_pressure})'

class PateMcad:
    # Static dict of servers
    _servers: dict[str, PateMcad] = {}

    def __init__(self, name: str, triple: str, cpu: str, port: int):
        self.name = name
        self.triple = triple
        self.cpu = cpu
        self.port = port
        self.proc = None
        self.channel = None
        self.stub = None

    @staticmethod
    def _get_triple_cpu_port(arch: str):
        if arch == "x86_64":
            return "x86_64-unknown-linux-gnu", "skylake", 50522

        elif arch == "armv7":
            return "armv7-linux-gnueabih", "cortex-a57", 50053

        elif arch == "thumb2":
            return "thumbv8", "cortex-a57", 50054

        elif arch == "aarch64":
            return "aarch64-unknown-linux-gnu", "cortex-a55", 50055

        else:
            return None

    @classmethod
    def getServerForArch(cls, arch: str) -> Optional[PateMcad]:
        server = cls._servers.get(arch)
        if server:
            return server
        else:
            triple, cpu, port = cls._get_triple_cpu_port(arch)
            if triple and cpu and port:
                server = PateMcad(arch, triple, cpu, port)
                server.start()
                cls._servers[arch] = server
                return server

    @classmethod
    def stopAllServers(cls):
        for server in cls._servers.values():
            server.stop()
        _servers = {}

    def isRunning(self) -> bool:
        return bool(self.proc)

    def start(self):
        if self.isRunning():
            # MCAD server already started.
            return

        # TODO: Make this a config var?
        dockerName = 'mcad-dev'
        # TODO: This is dependent on arch of docker image (eg apple silicon vs x86_64)
        brokerPluginPath = '/work/LLVM-MCA-Daemon/build/plugins/binja-broker/libMCADBinjaBroker.so'

        args = ['/usr/local/bin/docker',  # TODO: Path is os specific
                'run',
                '-p', f'{self.port}:50052',
                # Get rid of warning. We really want this platform, not native.
                '--platform=linux/amd64',
                # Remove the image from docker desktop on exit.
                '--rm',
                dockerName,
                # TODO: Do I really want debug?
                #'--debug',
                f'-mtriple={self.triple}',
                f'-mcpu={self.cpu}',
                # TODO: Ask about these three
                #'--use-call-inst',
                #'--use-return-inst',
                #'--noalias=false',
                f'-load-broker-plugin={brokerPluginPath}',
                ]
        self.proc = subprocess.Popen(args,
                                     # Create a new process group, so we can kill it cleanly
                                     preexec_fn=os.setsid,
                                     text=True, encoding='utf-8',
                                     stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT,
                                     )
        print(f'MCAD {self.name}: Server started')
        t = threading.Thread(target=_echoLines, args=[f'MCAD {self.name}:', self.proc.stdout], daemon=True)
        t.start()
        # TODO: Rather than sleep, wait for output from server indicating it is listening.
        time.sleep(2)
        self.channel = grpc.insecure_channel(f"localhost:{self.port}")
        self.stub = binja_pb2_grpc.BinjaStub(self.channel)

    def stop(self) -> None:
        if not self.isRunning():
            return

        # Asking for cycle counts with empty instruction list should cause server to exit
        print(f'MCAD {self.name}: Stopping server')
        self.request_cycle_counts([])
        self.proc = None
        self.channel = None
        self.stub = None

    def request_cycle_counts(self, instructions: list[bytes]) -> List[CycleCount]:
        if not self.isRunning:
            return []
        pbInstructions = map(lambda b: binja_pb2.BinjaInstructions.Instruction(opcode=b), instructions)
        pbCycleCounts = self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=pbInstructions))
        return list(map(lambda cc: CycleCount(cc.ready, cc.executed, cc.is_under_pressure), pbCycleCounts.cycle_count))


def _echoLines(pre: str, io: IO):
    for line in io:
        print(pre, line)








