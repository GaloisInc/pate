CC=arm-linux-gnueabi-gcc
OD=arm-linux-gnueabi-objdump
# from git@gitlab-ext.galois.com:pate/programtargets.git
CHALLENGE_10_BIN=$(CHALLENGE_DIR)/Challenge_10/build/program_c.gcc.vuln
CHALLENGE_10_PATCH=build/challenge10.bsdiff
EXTRA_TARGETS=

# add challenge10 as test if programtargets repo is checked out
ifeq (,$(wildcard ${CHALLENGE_10_BIN}))

else
EXTRA_TARGETS=challenge10.test
scripted/challenge10.original.exe: ${CHALLENGE_10_BIN}
	cp ${CHALLENGE_10_BIN} $@

scripted/challenge10.patched.exe: scripted/challenge10.original.exe ${CHALLENGE_10_PATCH}
	bspatch scripted/challenge10.original.exe scripted/challenge10.patched.exe ${CHALLENGE_10_PATCH}

challenge10.test: scripted/challenge10.original.exe scripted/challenge10.patched.exe
endif


#CC=arm-none-eabi-gcc
#OD=arm-none-eabi-objdump

include ../template.mk
