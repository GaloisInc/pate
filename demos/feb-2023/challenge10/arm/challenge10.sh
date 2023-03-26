#!/bin/bash
set -o xtrace
../../../../pate.sh -o challenge10.original.exe -p challenge10.patched.exe -b challenge10.toml --original-bsi-hints results_arm.json --patched-bsi-hints results_arm.json --original-csv-function-hints challenge10.csv --patched-csv-function-hints challenge10.csv -e ContinueAfterRecoverableFailures -s transport_handler -r AllowEqRescopeFailure --save-macaw-cfgs CFGs
