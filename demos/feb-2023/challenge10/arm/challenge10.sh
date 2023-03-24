#!/bin/bash
set -o xtrace
../../../../pate.sh -o challenge10.patched.exe -p challenge10.original.exe -b challenge10.toml --original-bsi-hints results_arm.json --patched-bsi-hints results_arm.json --original-csv-function-hints challenge10.csv --patched-csv-function-hints challenge10.csv -e ContinueAfterRecoverableFailures -s test_crypto -r AllowEqRescopeFailure
