# PATE Verifier Binary Ninja Plugin

This is an early release of the PATE plugin for Binary Ninja (Binja). At this time, there is no interface to specify PATE run parameters. You must create a run configuration file in json format. For example:
```json
{
  "original": "may23-challenge10.original.exe",
  "patched": "may23-challenge10.patched.exe",
  "args": [
           "-b may23-challenge10.toml",
           "--original-bsi-hints may23-challenge10.bsi-hints.json",
           "--patched-bsi-hints may23-challenge10.bsi-hints.json",
           "--original-csv-function-hints may23-challenge10.function-hints.csv",
           "--patched-csv-function-hints may23-challenge10.function-hints.csv",
           "-e ContinueAfterRecoverableFailures",
           "-r AllowEqRescopeFailure",
           "-s transport_handler",
           "--save-macaw-cfgs CFGs"
         ]
}         
```

There are several examples in the [PATE Binja Demos repo](https://gitlab-ext.galois.com/pate/pate-binja-demos).


## Installation

The plugin was developed on macOS. It should run on linux, but has not been tested (yet). It will not run on Windows due to process and path handling differences.

To use this plugin in Binja, put this directory (or a symlink to this directory) in:
- macOS: ~/Library/Application Support/Binary Ninja/plugins/
- Linux: ~/.binaryninja/plugins/

To run replays of the PATE Verifier you do not need any more configuration. 

If you want to run the PATE Verifier live, you need to install a PATE docker image or build PATE from source. See the [PATE project](https://github.com/GaloisInc/pate) for instructions. No environment variables are needed to run PATE docker. To run PATE built from source you do need to define these the environment variables:
```bash
export PATE=<pate source directory>
export PATE_BINJA_MODE=BUILD
```


## Running

Once Binary Ninja is running, you can run PATE from the "Plugins" menu. An open file dialog will open. By defualt it will be looking for a PATE Run Configuration file (*.run-config.json). If you want to run a replay file, select "PATE Replay (*.json)" in the file type drop down menu.


## MCAD Intigration

MCAD provides timing analysis for instruction traces. To enable this integration you need to do two things:

1. Install the MCAD docker image. See the Docker section here:
   https://github.com/securesystemslab/LLVM-MCA-Daemon?tab=readme-ov-file#docker. Use the `broker-improvements` branch.
2. In the Binary Ninja UI, got to Preferences. In the PATE section set name the MCAD docker image.

