.PHONY: all %.test

CC=powerpc64-linux-gnu-gcc
OD=powerpc64-linux-gnu-objdump

all: $(patsubst %c,%exe,$(wildcard *.c))

%.exe: %.s
	$(CC) -fno-stack-protector -nostdlib $< -o $@

%.s: %.c
	$(CC) -fno-stack-protector -S -c $< -o $@

%.test: %.original.exe %.patched.exe
	$(OD) -d $(basename $@).original.exe > $(basename $@).original.dump
	$(OD) -d $(basename $@).patched.exe > $(basename $@).patched.dump
	diff $(basename $@).original.dump $(basename $@).patched.dump


.PRECIOUS: %.s

clean:
	rm *.s *.exe
