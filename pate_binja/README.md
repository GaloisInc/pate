# PATE Verifier Plugin for Binary Ninja

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

To run the PATE Verifier live (docker or built from source) you need to start Binja from a bash shell because it needs your bash environment. For example, on macOS:
```bash
open /Applications/Binary\ Ninja.app
```
If you only want to run replays, you can launch Binary Ninja from the macOS Dock.

Once Binary Ninja is running, you can run PATE from the "Plugins" menu. An open file dialog will open. By defualt it will be looking for a PATE Run Configuration file (*.run-config.json). If you want to run a replay file, select "PATE Replay (*.json)" in the file type drop down menu.


## Developer Notes (macOS with PyCharm Pro)

You must launch PyCharm Pro from a bash shell because it needs your bash environment. For example, on macOS:
```bash
open /Applications/PyCharm.app
```

To install the Binja api for completion in PyCharm:

- Setup project with venv (Python 3.11 or newer)
- Go to python console (runs within venv)
- python /Applications/Binary\ Ninja.app/Contents/Resources/scripts/install_api.py 

To setup debugging:

- See https://docs.binary.ninja/dev/plugins.html#remote-debugging-with-intellij-pycharm
- In Binja settings specify python interpreter and site package dir to point at your Pycharm project venv installs.
- Create the run config. Note "pip install ..." command line for next step. Pick a port.
- In Pycharm python console (venv) execute the "pip install ..." command.
- May also need/want to set python interpreter and site packages in Binary Ninja settings to the venv for the pyCharm project.
