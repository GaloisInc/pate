.PHONY: all %.test

CC=arm-linux-gnueabi-gcc
OD=arm-linux-gnueabi-objdump

all: $(patsubst %c,%exe,$(wildcard *.c)) $(patsubst %c,%i,$(wildcard *.c))

%.i: %.c
	$(CC) -fno-stack-protector -nostdlib $< -E -o $@

%.exe: %.s link.ld
	$(CC) -fno-stack-protector -nostdlib link.ld $< -o $@

%.s: %.c
	$(CC) -fno-stack-protector -S -c $< -o $@

%.test: %.original.exe %.patched.exe
	$(OD) -d $(basename $@).original.exe > $(basename $@).original.dump
	$(OD) -d $(basename $@).patched.exe > $(basename $@).patched.dump
	diff $(basename $@).original.dump $(basename $@).patched.dump


.PRECIOUS: %.s

clean:
	rm *.s *.exe
