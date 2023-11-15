.PHONY: target4-patch1 target4 target4-self target1-self target3 target3-self

target4.original.exe:
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/build/Amp_Chal_IDPS_Unpatched.ino.elf" $@

target4-master:
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/build/Amp_Chal_IDPS_Patched.ino.elf" $@

target4-room_1011_dendy:
	cd "$(HACKATHON_NOV_2023)" && git fetch && git checkout room_1011_dendy
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/Amp_Chal_IDPS_Ghidra_patched_r3.ino.elf" target4.patched.exe

target4-self: target4.original.exe target4.csv
	../../pate.sh \
	  --ignore-segments 1 \
	  --read-only-segments 3 \
	  -o target4.original.exe \
		-p target4.original.exe \
		-b target4.toml \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s get_bitchunk \
		--original-csv-function-hints target4.csv \
		--patched-csv-function-hints target4.csv \
		--save-macaw-cfgs target4_CFGs

target4: target4.original.exe target4.patched.exe target4.csv
	../../pate.sh \
	  --ignore-segments 1 \
	  --read-only-segments 3 \
	  -o target4.original.exe \
		-p target4.patched.exe \
		-b target4.toml \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s get_bitchunk \
		--original-csv-function-hints target4.csv \
		--patched-csv-function-hints target4.csv \
		--save-macaw-cfgs target4_CFGs

target4.diff: target4.original.exe target4.patched.exe
	arm-none-eabi-objdump -M force-thumb-mode -d target4.original.exe > target4.original.dump
	arm-none-eabi-objdump -M force-thumb-mode -d target4.patched.exe > target4.patched.dump
	diff target4.original.dump target4.patched.dump > target4.diff

target1.original.exe:
	cp "$(HACKATHON_NOV_2023)/Target 1 - NASA Lunar Relay Sat (powerpc)/cpu1/core-cpu1" $@

target1-self: target1.original.exe
	../../pate.sh \
	  -o target1.original.exe \
		-p target1.original.exe \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s main \
		--save-macaw-cfgs target1_CFGs

target3.original.so:
	cp "$(HACKATHON_NOV_2023)/Target 3 - MRZR Vehicle Interface Controller (BBB)/bin/libroscpp.so" $@

target3.patched.so:
	cp "$(HACKATHON_NOV_2023)/Target 3 - MRZR Vehicle Interface Controller (BBB)/bin/libroscpp_manually_patched.so" $@

target3-self: target3.original.so
	../../pate.sh \
	  --ignore-segments 1 \
	  -o target3.original.so \
		-p target3.original.so \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s main \
		--save-macaw-cfgs target1_CFGs

target3: target3.original.so target3.patched.so
	../../pate.sh \
	  --ignore-segments 1 \
	  -o target3.original.so \
		-p target3.patched.so \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s main \
		--save-macaw-cfgs target1_CFGs