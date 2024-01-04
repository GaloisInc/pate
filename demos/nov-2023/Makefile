.PHONY: target4-patch1 target4 target4-self target1-self target3 target3-self target3-room_1011_dendy target4-room_1011_dendy target4-master

PATE=../../pate.sh
#PATE=docker run --rm -it -v `pwd`:/demos pate

DEMOS=.
#DEMOS=/demos

main: $(HACKATHON_NOV_2023)/.git/HEAD
	cd "$(HACKATHON_NOV_2023)" && git fetch && git checkout main
	cat $(HACKATHON_NOV_2023)/.git/HEAD > main

room_1011_dendy: $(HACKATHON_NOV_2023)/.git/HEAD
	cd "$(HACKATHON_NOV_2023)" && git fetch && git checkout room_1011_dendy
	cat $(HACKATHON_NOV_2023)/.git/HEAD > room_1011_dendy

room1018: $(HACKATHON_NOV_2023)/.git/HEAD
	cd "$(HACKATHON_NOV_2023)" && git fetch && git checkout room1018
	cat $(HACKATHON_NOV_2023)/.git/HEAD > room1018

target4.original.exe: main
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/build/Amp_Chal_IDPS_Unpatched.ino.elf" $@

target4-room_1011_dendy: room_1011_dendy
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/Amp_Chal_IDPS_Ghidra_patched_r3.ino.elf" target4.patched.exe

target4-self: target4.original.exe target4.csv
	$(PATE) \
	  --ignore-segments 1 \
	  --read-only-segments 3 \
	  -o $(DEMOS)/target4.original.exe \
		-p $(DEMOS)/target4.original.exe \
		-b $(DEMOS)/target4.toml \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s get_bitchunk \
		--original-csv-function-hints $(DEMOS)/target4.csv \
		--patched-csv-function-hints $(DEMOS)/target4.csv \
		--save-macaw-cfgs $(DEMOS)/target4_CFGs

target4: target4.original.exe target4.patched.exe
	$(PATE) \
	  --ignore-segments 1 \
	  --read-only-segments 3 \
	  -o $(DEMOS)/target4.original.exe \
		-p $(DEMOS)/target4.patched.exe \
		-b $(DEMOS)/target4.toml \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s get_bitchunk \
		--original-csv-function-hints $(DEMOS)/target4.csv \
		--patched-csv-function-hints $(DEMOS)/target4.csv \
		--save-macaw-cfgs $(DEMOS)/target4_CFGs

target4.diff: target4.original.exe target4.patched.exe
	arm-none-eabi-objdump -M force-thumb-mode -d target4.original.exe > target4.original.dump
	arm-none-eabi-objdump -M force-thumb-mode -d target4.patched.exe > target4.patched.dump
	diff target4.original.dump target4.patched.dump > target4.diff

target1.original.exe: main
	cp "$(HACKATHON_NOV_2023)/Target 1 - NASA Lunar Relay Sat (powerpc)/cpu1/core-cpu1" $@

target1-self: target1.original.exe
	$(PATE) \
	  -o $(DEMOS)/target1.original.exe \
		-p $(DEMOS)/target1.original.exe \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s main \
		--save-macaw-cfgs $(DEMOS)/target1_CFGs

target1-exe: target1.original.exe target1.patched.exe
	$(PATE) \
	  -o $(DEMOS)/target1.original.exe \
		-p $(DEMOS)/target1.patched.exe \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s main \
		--save-macaw-cfgs $(DEMOS)/target1_CFGs

target1.original.so: main
	cp "$(HACKATHON_NOV_2023)/Target 1 - NASA Lunar Relay Sat (powerpc)/cpu1/cf/rr.so" $@

target1-room1018: room1018
	cp "$(HACKATHON_NOV_2023)/Target 1 - NASA Lunar Relay Sat (powerpc)/cpu1/cf/rr_patched.so" target1.patched.so

target1-so-self: target1.original.so
	$(PATE) \
	  -o $(DEMOS)/target1.original.so \
		-p $(DEMOS)/target1.original.so \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s RR_Init \
		-s RR_ReadTlmInput \
		-s RR_tohex \
		-s deregister_tm_clones \
		--save-macaw-cfgs $(DEMOS)/target1_CFGs

target1: target1.original.so target1.patched.so
	$(PATE) \
	  -o $(DEMOS)/target1.original.so \
		-p $(DEMOS)/target1.patched.so \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s RR_Init \
		-s RR_ReadTlmInput \
		-s RR_tohex \
		--save-macaw-cfgs $(DEMOS)/target1_CFGs

target3.original.so: main
	cp "$(HACKATHON_NOV_2023)/Target 3 - MRZR Vehicle Interface Controller (BBB)/bin/libroscpp.so" $@

target3-patched-master: main
	cp "$(HACKATHON_NOV_2023)/Target 3 - MRZR Vehicle Interface Controller (BBB)/bin/libroscpp_manually_patched.so" target3.patched.so

target3-room_1011_dendy: room_1011_dendy
	cp "$(HACKATHON_NOV_2023)/Target 3 - MRZR Vehicle Interface Controller (BBB)/patched_target3_irene_patcherex" target3.patched.so

target3-self: target3.original.so
	$(PATE) \
	  -o $(DEMOS)/target3.original.so \
		-p $(DEMOS)/target3.original.so \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s _ZN3ros22TransportPublisherLink15onMessageLengthERKN5boost10shared_ptrINS_10ConnectionEEERKNS1_12shared_arrayIhEEjb \
		-s _ZN3ros22TransportPublisherLink16onHeaderReceivedERKN5boost10shared_ptrINS_10ConnectionEEERKNS_6HeaderE \
		-s _ZN3ros22TransportPublisherLinkD2Ev \
		--save-macaw-cfgs $(DEMOS)/target1_CFGs

target3: target3.original.so target3.patched.so
	$(PATE) \
	  -o $(DEMOS)/target3.original.so \
		-p $(DEMOS)/target3.patched.so \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s _ZN3ros22TransportPublisherLink15onMessageLengthERKN5boost10shared_ptrINS_10ConnectionEEERKNS1_12shared_arrayIhEEjb \
		-s _ZN3ros22TransportPublisherLink16onHeaderReceivedERKN5boost10shared_ptrINS_10ConnectionEEERKNS_6HeaderE \
		-s _ZN3ros22TransportPublisherLinkD2Ev \
		--save-macaw-cfgs $(DEMOS)/target1_CFGs

target3.diff: target3.original.so target3.patched.so
	arm-none-eabi-objdump -M force-thumb-mode -d target3.original.so > target3.original.dump
	arm-none-eabi-objdump -M force-thumb-mode -d target3.patched.so > target3.patched.dump
	diff target3.original.dump target3.patched.dump > target3.diff