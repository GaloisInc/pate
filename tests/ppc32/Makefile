.PHONY: all %.test

CC=powerpc-linux-gnu-gcc
OD=powerpc-linux-gnu-objdump

all: $(notdir $(patsubst %original.c,%test,$(wildcard ../src/*.original.c))) $(addprefix ./build/,$(notdir $(patsubst %c,%i,$(wildcard ../src/*.c))))

./build:
	mkdir -p $@

./unequal:
	mkdir -p $@

./build/%.i: ../src/%.c | ./build
	$(CC) -fno-stack-protector -nostdlib $< -E -o $@

%.exe: ./build/%.s ../src/link.ld
	$(CC) -fno-stack-protector -nostdlib ../src/link.ld $< -o $@

./unequal/%.original.exe: %.original.exe | ./unequal
	cp $(basename $(basename $<)).original.exe ./unequal/

./unequal/%.patched.exe: %.patched-bad.exe ./unequal/%.original.exe | ./unequal
	mv $< $@

./build/%.s: ../src/%.c | ./build
	$(CC) -fno-stack-protector -S -c $< -o $@

%.test: %.original.exe %.patched.exe ./unequal/%.patched.exe
	$(OD) -d $(basename $@).original.exe > ./dumps/$(basename $@).original.dump
	$(OD) -d $(basename $@).patched.exe > ./dumps/$(basename $@).patched.dump
	$(OD) -d ./unequal/$(basename $@).patched.exe > ./dumps/$(basename $@).patched-bad.dump
	diff ./dumps/$(basename $@).original.dump ./dumps/$(basename $@).patched.dump || true
	diff ./dumps/$(basename $@).original.dump ./dumps/$(basename $@).patched-bad.dump || true

.PRECIOUS: ./build/%.s ./build/%.i %.exe ./unequal/%.original.exe ./unequal/%.patched.exe

clean:
	-rm ./build/*.s ./build/*.i

realclean: clean
	-rm *.exe
	-rm ./unequal/*.exe
