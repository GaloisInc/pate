#!/bin/bash
echo "Original:"
cat demo3.original.c
echo "Patched:"
cat demo3.patched.c

set -x
cabal v2-run exe:pate -- --arch PPC -o demo3.original.exe -p demo3.patched.exe
