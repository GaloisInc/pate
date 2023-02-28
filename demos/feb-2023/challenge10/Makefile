.PHONY: all

%.exe: %.exe.bsdiff $(CHALLENGE_DIR)/Challenge_10/mpc5777c_dev_c10/Debug_FLASH/mpc5777c_dev_c10.elf
	bspatch $(CHALLENGE_DIR)/Challenge_10/mpc5777c_dev_c10/Debug_FLASH/mpc5777c_dev_c10.elf $@ $<

all: challenge10.original.exe challenge10.patched.exe