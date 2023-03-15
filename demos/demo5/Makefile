.PHONY: all native

CC=arm-none-eabi-gcc
OD=arm-none-eabi-objdump
FLAGS=--specs=nosys.specs

%.exe: ./%.c
	$(CC) $(FLAGS) $< -o $@

%.native.exe: ./%.c
	gcc $< -o $@

diff: all
	$(OD) -d demo5.original.exe > original.dump
	$(OD) -d demo5.patched.exe > patched.dump
	(diff original.dump patched.dump || true)

all: demo5.original.exe demo5.patched.exe
native: demo5.original.native.exe demo5.patched.native.exe
