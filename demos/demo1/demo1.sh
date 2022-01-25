#!/bin/bash
echo "Original:"
cat demo1.original.c
echo "Patched:"
cat demo1.patched.c

set -x
cabal v2-run exe:pate -- --arch PPC -o demo1.original.exe -p demo1.patched.exe
