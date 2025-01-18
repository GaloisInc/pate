ROOT_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

CC=docker run --rm -it -v $(ROOT_DIR):/z --workdir="/z" ubuntu-build clang
OD=docker run --rm -it -v $(ROOT_DIR):/z --workdir="/z" ubuntu-build objdump

PATE=$(ROOT_DIR)/../../../pate.sh

all: packet.original.exe packet.patched.exe packet.patched-bad.exe

.PHONY: all clean %.diff
.SECONDARY: packet.original.dump packet.patched.dump packet.patched-bad.dump

clean:
	rm -f packet.original.exe packet.patched.exe packet.patched-bad.exe packet.original.dump packet.patched.dump packet.patched-bad.dump

docker: Dockerfile
	docker build -t ubuntu-build -f $< .

packet.original.exe: packet.c | docker
	$(CC) -O0 packet.c -o $@

packet.patched.exe: packet.c | docker 
	$(CC) -O0 -DGOODPATCH=1 packet.c -o $@

packet.patched-bad.exe: packet.c | docker
	$(CC) -O0 -DBADPATCH=1 packet.c -o $@

%.dump: %.exe
	$(OD) -d $(basename $@).exe > ./$(basename $@).dump

%.diff: %.dump packet.original.dump
	diff packet.original.dump $(word 1,$^) || true

run: packet.original.exe packet.patched.exe packet.pate
	$(PATE) --original packet.original.exe --patched packet.patched.exe -s parse_packet --script packet.pate

run-bad: packet.original.exe packet.patched-bad.exe packet.pate
	$(PATE) --original packet.original.exe --patched packet.patched-bad.exe -s parse_packet --script packet.pate