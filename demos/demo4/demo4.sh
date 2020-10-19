#!/bin/bash
echo "Original:"
cat demo4.original.c
echo "Patched:"
cat demo4.patched.c

set -x
cabal v2-run pate-exec -- --arch PPC -o demo4.original.exe -p demo4.patched.exe
