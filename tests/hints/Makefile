all: $(patsubst %.c,%.elf,$(wildcard *.c))

%.elf: %.c
	gcc -g -O0 -nostdlib -o $@ $<
