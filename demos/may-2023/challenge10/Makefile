.PHONY: all run run_docker
all: challenge10.original.exe challenge10.patched.exe

.INTERMEDIATE: $(CHALLENGE_DIR)/Challenge_10/build/program_c.gcc.vuln

challenge10.original.exe: $(CHALLENGE_DIR)/Challenge_10/build/program_c.gcc.vuln
	cp $< $@

challenge10.patched.exe: challenge10.original.exe challenge10.bsdiff
	bspatch $< $@ challenge10.bsdiff


run: challenge10.patched.exe
	../../../pate.sh \
	  -o challenge10.original.exe \
		-p challenge10.patched.exe \
		-b challenge10.toml \
		--original-bsi-hints challenge10.json \
		--patched-bsi-hints challenge10.json \
		--original-csv-function-hints challenge10.csv \
		--patched-csv-function-hints challenge10.csv \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s transport_handler \
		--save-macaw-cfgs CFGs \
        ${EXTRA_FLAGS}

run_json: EXTRA_FLAGS = --json-toplevel
run_json: run
