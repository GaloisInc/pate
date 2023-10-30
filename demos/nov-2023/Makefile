.PHONY: target4 target4-self

target4.original.exe:
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/build/Amp_Chal_IDPS_Unpatched.ino.elf" $@

target4.patched.exe:
	cp "$(HACKATHON_NOV_2023)/Target 4 - Grid IDPS (ARM Cortex M7)/build/Amp_Chal_IDPS_Patched.ino.elf" $@

target4-self: target4.original.exe
	../../pate.sh \
	  --ignore-segments 1 \
	  -o target4.original.exe \
		-p target4.original.exe \
		-b target4.toml \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s entry1 \
		--original-csv-function-hints target4.csv \
		--patched-csv-function-hints target4.csv \
		--save-macaw-cfgs target4_CFGs

target4: target4.original.exe target4.patched.exe
	../../pate.sh \
	  -o target4.original.exe \
		-p target4.patched.exe \
		-b target4.toml \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s entry1 \
		--original-csv-function-hints target4.csv \
		--patched-csv-function-hints target4.csv \
		--save-macaw-cfgs target4_CFGs