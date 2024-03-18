CC=arm-linux-gnueabi-gcc
OD=arm-linux-gnueabi-objdump
# from git@gitlab-ext.galois.com:pate/programtargets.git
CHALLENGE_10_BIN=$(CHALLENGE_DIR)/Challenge_10/build/program_c.gcc.vuln
EXTRA_TARGETS=()

# add challenge10 as test if programtargets repo is checked out
ifeq (,$(wildcard ${CHALLENGE_10_BIN}))

else
EXTRA_TARGETS+=scripted/challenge10.test
scripted/challenge10.original.exe: ${CHALLENGE_10_BIN}
	cp $< $@
endif


TARGET_7_BIN=$(CHALLENGE_DIR)/Hackathon_Spring_24/GridIDPS/build/amp_challenge_arm.ino_unstripped.elf
ifeq (,$(wildcard ${TARGET_7_BIN}))
else
EXTRA_TARGETS+=scripted/target7.test
scripted/target7.original.exe: ${TARGET_7_BIN}
	cp $< $@
endif

scripted/%.patched.exe: scripted/%.original.exe build/%.bsdiff
	bspatch $< $@ $(word 2,$^)

.PHONY: scripted/%.test

scripted/%.test: scripted/%.original.exe scripted/%.patched.exe
	true

.PHONY: scripted/%.script_run


.SECONDEXPANSION:
scripted/%.script_run: scripted/%.test scripted/%.args $$(wildcard $$*.toml) $$(wildcard $$*.csv)
	cd scripted; \
	../../../pate.sh $(shell cat $(word 2,$^))


#CC=arm-none-eabi-gcc
#OD=arm-none-eabi-objdump

include ../template.mk
