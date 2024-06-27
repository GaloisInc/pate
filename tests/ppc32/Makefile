CC=powerpc-linux-gnu-gcc
OD=powerpc-linux-gnu-objdump
EXTRA_TARGETS=

ifeq (,$(wildcard $(CHALLENGE_DIR)))
else

EXTRA_TARGETS+=scripted/target1

scripted/target1.%: ../.programtargets
	$(call fetch,target1)

endif

.PHONY: scripted/target1

scripted:
	mkdir -p scripted

scripted/target1: scripted scripted/target1.original.exe scripted/target1.args scripted/target1.pate

scripted/target1.script_run: scripted/target1
	cd scripted; \
	../../../pate.sh $(shell cat scripted/target1.args)

include ../template.mk
