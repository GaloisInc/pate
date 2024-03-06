.PHONY: main target7-self target7-%

ifdef json
  JSON_FLAG=--json-toplevel
endif

ifdef docker
  ifdef json
    # Don't run with terminal when using json interface
    PATE=docker run --rm -i -v .:/work --workdir=/work pate $(JSON_FLAG)
  else
    PATE=docker run --rm -it -v .:/work --workdir=/work pate $(JSON_FLAG)
  endif
else
  PATE=../../pate.sh $(JSON_FLAG)
endif

main: $(HACKATHON_MAR_2024)/.git/HEAD
	cd "$(HACKATHON_MAR_2024)" && git fetch && git checkout main
	cat $(HACKATHON_MAR_2024)/.git/HEAD > main

target7.original.exe: main
	cp "$(HACKATHON_MAR_2024)/GridIDPS/build/amp_challenge_arm.ino_unstripped.elf" $@

target7.%.exe: target7.original.exe target7.%.bsdiff
	bspatch $< $@ $(word 2,$^)

target7-self: target7.original.exe
	$(PATE) \
	  --ignore-segments 1 \
	  -o 	target7.original.exe \
		-p target7.original.exe \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s _ZN6SDFile13setModifyTimeERK14DateTimeFields \
		--save-macaw-cfgs target7_CFGs \
		--script target7.original.pate

target7-%: target7.%.exe target7.%.pate target7.original.exe
	$(PATE) \
		--ignore-segments 1 \
		-o 	target7.original.exe \
		-p $(word 1,$^) \
		-e ContinueAfterRecoverableFailures \
		-r AllowEqRescopeFailure \
		-s _ZN6SDFile13setModifyTimeERK14DateTimeFields \
		--save-macaw-cfgs target7_CFGs \
		--script $(word 2,$^)

target7.%.dump: target7.%.exe
	arm-none-eabi-objdump -M force-thumb-mode -d $^ > $@

target7.%.diff: target7.original.dump target7.%.dump 
	diff $^ > $@ || true