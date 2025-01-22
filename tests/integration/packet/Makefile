ROOT_DIR := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))

CC=docker run --rm -it -v $(ROOT_DIR):/z --workdir="/z" ubuntu-build clang
OD=docker run --rm -it -v $(ROOT_DIR):/z --workdir="/z" ubuntu-build objdump

PATE=$(ROOT_DIR)/../../../pate.sh

all: packet.original.exe packet.patched.exe

.PHONY: all clean %.diff
.SECONDARY: packet.original.dump packet.patched.dump

clean:
	rm -f packet.original.exe packet.patched.exe packet.original.dump packet.patched.dump

docker: Dockerfile
	docker build -t ubuntu-build -f $< .

packet.original.exe: packet.c | docker
	$(CC) -O0 packet.c -o $@

packet.patched.exe: packet.c | docker 
	$(CC) -O0 -DPATCHED=1 packet.c -o $@

%.dump: %.exe
	$(OD) -d $(basename $@).exe > ./$(basename $@).dump

%.diff: %.dump packet.original.dump
	diff packet.original.dump $(word 1,$^) || true

run: packet.original.exe packet.patched.exe
	$(PATE) --original packet.original.exe --patched packet.patched.exe -s parse_packet --add-trace-constraints