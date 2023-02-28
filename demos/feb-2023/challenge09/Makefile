.PHONY: all

%.exe: %.exe.bsdiff $(CHALLENGE_DIR)/Challenge_09/build/program_c.gcc.vuln
	bspatch $(CHALLENGE_DIR)/Challenge_09/build/program_c.gcc.vuln $@ $<

all: challenge09.original.exe challenge09.patched.exe