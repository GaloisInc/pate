.PHONY: all %.test %.copy

extras: ${EXTRA_TARGETS}

all: $(notdir $(patsubst %original.c,%test,$(wildcard ../src/*.original.c))) $(addprefix ./build/,$(notdir $(patsubst %c,%i,$(wildcard ../src/*.c)))) extras

./unequal:
	mkdir -p $@

./dumps:
	mkdir -p $@

./build/%.i: ../src/%.c
	$(CC) -fno-stack-protector -nostdlib $< -E -o $@

malloc-%.exe: ./build/malloc-%.s ./build/link.ld
	$(CC) -fno-stack-protector -nostartfiles ./build/link.ld $< -o $@

%.exe: ./build/%.s ./build/link.ld
	$(CC) -fno-stack-protector -nostdlib ./build/link.ld $< -o $@

./unequal/%.original.exe: %.original.exe | ./unequal
	cp $(basename $(basename $<)).original.exe ./unequal/

./unequal/%.patched.exe: %.patched-bad.exe ./unequal/%.original.exe | ./unequal
	mv $< $@

./build/%.s: ../src/%.c
	$(CC) -fno-stack-protector -S -c $< -o $@

%.copy: ../src/%.original.c
	cp $< ../src/$*.patched.c
	cp $< ../src/$*.patched-bad.c

%.test: %.original.exe %.patched.exe ./unequal/%.patched.exe | ./dumps
	$(OD) -d $(basename $@).original.exe > ./dumps/$(basename $@).original.dump
	$(OD) -d $(basename $@).patched.exe > ./dumps/$(basename $@).patched.dump
	$(OD) -d ./unequal/$(basename $@).patched.exe > ./dumps/$(basename $@).patched-bad.dump
	diff ./dumps/$(basename $@).original.dump ./dumps/$(basename $@).patched.dump || true
	diff ./dumps/$(basename $@).original.dump ./dumps/$(basename $@).patched-bad.dump || true

%.test_run: %.original.exe %.patched.exe
	../../pate.sh -o $(basename $@).original.exe -p $(basename $@).patched.exe \
		`( (test -f $(basename $@).toml && echo "-b $(basename $@).toml") || echo "")` \
		`( (test -f $(basename $@).pate && echo "--script $(basename $@).pate") || echo "")`

.PRECIOUS: ./build/%.s ./build/%.i %.exe malloc-%.exe ./unequal/%.original.exe ./unequal/%.patched.exe

clean:
	-rm -f ./build/*.s 
	-rm -f ./build/*.i

realclean: clean
	-rm -f *.exe
	-rm -f ./unequal/*.exe
