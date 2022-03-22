CC=powerpc64-linux-gnu-gcc

.PHONY: demo1
demo1: demo1/demo1.original.i demo1/demo1.patched.i
	cabal v2-run exe:pate -- --arch PPC \
                                --original demo1/demo1.original.exe \
                                --patched demo1/demo1.patched.exe \
                                --interactive \
                                --original-source demo1/demo1.original.i \
                                --patched-source demo1/demo1.patched.i

.PHONY: demo2
demo2: demo2/demo2.original.i demo2/demo2.patched.i
	cabal v2-run exe:pate -- --arch PPC \
                                --original demo2/demo2.original.exe \
                                --patched demo2/demo2.patched.exe \
                                --interactive \
                                --original-source demo2/demo2.original.i \
                                --patched-source demo2/demo2.patched.i

.PHONY: demo3
demo3: demo3/demo3.original.i demo3/demo3.patched.i
	cabal v2-run exe:pate -- --arch PPC \
                                --original demo3/demo3.original.exe \
                                --patched demo3/demo3.patched.exe \
                                --interactive \
                                --original-source demo3/demo3.original.i \
                                --patched-source demo3/demo3.patched.i

.PHONY: demo4
demo4: demo4/demo4.original.i demo4/demo4.patched.i
	cabal v2-run exe:pate -- --arch PPC \
                                --original demo4/demo4.original.exe \
                                --patched demo4/demo4.patched.exe \
                                --interactive \
                                --original-source demo4/demo4.original.i \
                                --patched-source demo4/demo4.patched.i

.PHONY: inlining
inlining: ../tests/ppc/test-direct-calls.original.i ../tests/ppc/test-direct-calls.patched.i
	cabal v2-run exe:pate -- --arch PPC \
                                --original ../tests/ppc/test-direct-calls.original.exe \
                                --patched ../tests/ppc/test-direct-calls.patched.exe \
                                --interactive \
                                --original-source ../tests/ppc/test-direct-calls.original.i \
                                --patched-source ../tests/ppc/test-direct-calls.patched.i
.PHONY: challenge02
challenge02: challenge02/challenge-02.original.exe challenge02/challenge-02.patched.exe
	cabal v2-run exe:pate -- \
                                --original challenge02/challenge-02.original.exe \
                                --patched challenge02/challenge-02.patched.exe

.PHONY: challenge02-self
challenge02-self: challenge02/challenge-02.original.exe challenge02/challenge-02.original.exe
	cabal v2-run exe:pate -- \
                                --original challenge02/challenge-02.original.exe \
                                --patched challenge02/challenge-02.original.exe

.PHONY: challenge03
challenge03: challenge03-variant/challenge03.orig.exe challenge03-variant/challenge03.patched.exe challenge03-variant/challenge03.toml
	cabal v2-run exe:pate -- \
		                       --original $(word 1,$^) \
							   --patched $(word 2,$^) \
							   --blockinfo $(word 3,$^) \
							   --log-file challenge03.out \
							   --verbosity Debug \
							   --noproofs \
							   --ignoremain

.PHONY: abort
abort: abort/test-abort.original.exe abort/test-abort.patched.exe abort/test-abort.hints.csv
	cabal v2-run exe:pate -- \
		                       --original abort/test-abort.original.exe \
	                           --patched abort/test-abort.patched.exe \
							   --original-csv-function-hints abort/test-abort.hints.csv
%.i: %.c
	$(CC) -fno-stack-protector -nostdlib $< -E -o $@
