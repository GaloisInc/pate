#!/bin/bash
echo "Original:"
cat demo2.original.c
echo "Patched:"
cat demo2.patched.c

set -x
cabal v2-run exe:pate -- --arch PPC -o demo2.original.exe -p demo2.patched.exe
