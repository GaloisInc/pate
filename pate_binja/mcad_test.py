# Scratch file for testing MCAD interface in isolation.

import grpc

import mcad.PateMcad
from mcad import binja_pb2_grpc, binja_pb2

class grpc_client:
    def __init__(self):
        #self.channel = grpc.insecure_channel("localhost:50052")  # x86_64
        self.channel = grpc.insecure_channel("localhost:50053")  # armv7
        #self.channel = grpc.insecure_channel("localhost:50054")  # thumb2
        #self.channel = grpc.insecure_channel("localhost:50055")  # aaarch64
        self.stub = binja_pb2_grpc.BinjaStub(self.channel)

    # mov    rbx,rcx
    # add    rax,rbx
    # sub    rax,rcx
    def send_instructions(self):
        insn_1 = binja_pb2.BinjaInstructions.Instruction(opcode=bytes(bytearray([0x48, 0x01, 0xD8])))
        insn_2 = binja_pb2.BinjaInstructions.Instruction(opcode=bytes(bytearray([0x48, 0x89, 0xCB])))
        insn_3 = binja_pb2.BinjaInstructions.Instruction(opcode=bytes(bytearray([0x48, 0x29, 0xC8])))
        instructions = [insn_1, insn_2, insn_3]
        print(instructions)
        return self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=instructions))

    # mov    rbx,rcx
    # add    rax,rbx
    # cdqe / syscall
    def send_instructions2(self):
        insn_1 = binja_pb2.BinjaInstructions.Instruction(opcode=bytes(bytearray([0x48, 0x01, 0xD8])))
        insn_2 = binja_pb2.BinjaInstructions.Instruction(opcode=bytes(bytearray([0x48, 0x89, 0xCB])))
        insn_3 = binja_pb2.BinjaInstructions.Instruction(opcode=bytes(bytearray([0x0f, 0x05])))
        instructions = [insn_1, insn_2, insn_3]
        print(instructions)
        return self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=instructions))

    def send_instructions3(self):
        # thumb2 error?
        instructions = []

        #thumb2
        # instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\xb4\xee\xc0{')))

        #thumb2
        # instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\x00(\x03\xd0')))
        # instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\x03\xd0\xbd\xe8')))

        #thumb2
        # instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\x1bH')))
        # instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'xD')))
        # instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\xff\xf7\xfa\xe8')))

        # armv7
        #instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\xbd\xe8\xff@')))
        #instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\xc6\xf70\xba')))
        #instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\x1bHxD')))
        #instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'')))
        #instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\xff\xf7\xfa\xe8')))

        # Bug? thumb2
        instructions.append(binja_pb2.BinjaInstructions.Instruction(opcode=bytes(b'\x0b\xf0\xd5\xf9')))

        print(instructions)
        return self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=instructions))

    def send_empty(self):
        self.stub.RequestCycleCounts(binja_pb2.BinjaInstructions(instruction=[]))

G = grpc_client()
# response = G.send_instructions1()
# print('Counts:', response)
# response = G.send_instructions2()
# print('Counts:', response)
response = G.send_instructions3()
print('Counts:', response)
