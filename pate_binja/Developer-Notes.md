# Developer Notes for the PATE Verifier Binary Ninja Plugin


## Files and Directories

- `.idea` - Project file for PyCharm.
- `mcad/` - Code for MCAD integration.
  - `binja.proto` - GRPC proto specification for communications between MCAD and the PATE Verifier Binary Ninja Plugin.
  - `binja-pb2.py` - Code generated by GRPC from `binja.proto'.
  - `binja_pb2_grpc.py` - Code generated by GRPC from `binja.proto'.
  - `PateMcad.py` - Python code wrapping the MCAD GRPC communications.
- `Developer-Notes.md` - This file.
- `mcad_test.py` - Scratch file for testing MCAD interface in isolation.
- `pate.py` - Wrapper for the PATE verifier. Handles startup, shutdown and I/O with the PATE Verifier. This code is independent of the GUI and can be run standalone in tty mode.
- `README.md` - Instructions to install and use the PATE Verifier Binary Ninja Plugin.
- `run-pate.sh` - Shell script used to start the PATE Verifier either natively or under docker.
- `run_pate_demo.log` - Logfile written when running in tty mode from the PyCharm environment. This file is not in the repository.
- `run_pate_demo.py` - Run the PATE Verifier Binary Ninja Plugin in tty mode, independently of Binary Ninja.
- `view.py` - The GUI code for the PATE Verifier Binary Ninja Plugin.
  

## Development Environment

This software was developed on MacOS with the PyCharm development Environment.

To install the Binja api for completion in PyCharm:

- Setup project with venv (Python 3.11 or newer)
- Go to python console (runs within venv)
- python /Applications/Binary\ Ninja.app/Contents/Resources/scripts/install_api.py 

To set up debugging under Binary Ninja (requires PyCharm Pro):

- See https://docs.binary.ninja/dev/plugins.html#remote-debugging-with-intellij-pycharm
- In Binja settings specify python interpreter and site package dir to point at your PyCharm project venv installs.
- Create the run config. Note "pip install ..." command line for next step. Pick a port.
- In PyCharm python console (venv) execute the "pip install ..." command.
- May also need/want to set python interpreter and site packages in Binary Ninja settings to the venv for the pyCharm project.

Debugging while running under Binja is not very helpfull as the GUI event loop is not running under the debugger. Thus it is only useful for code invoked from the Binja Python console. Also see the 'TTY Mode for Debugging' section below. 


## TTY Mode

Two modes are supported, tty and GUI. The reason for the tty mode is to provide full access to the PyCharm debugger. To run demos in tty mode, you need to define an environment variable to point at the clone of the [PATE Binja Demos repo](https://gitlab-ext.galois.com/pate/pate-binja-demos):

```bash
export PATE_BINJA_DEMOS=<demos dir>
```

In tty mode, non of the GUI code in `view.py` is run. Being abel to run the done under tty or GUI is supported by the `pate.PateUserInteraction` abstract class. The `pate.PateWrapper` uses this to interact with the user without any knowlege about the tty or GUI interface. There are two implementations of this abstract class that support these two modes: `pate.TtyUserInteraction` and `view.GuiUserInteraction`.

## Threading Model

The Pate Verifier Binary Ninja Plugin has these threads:

- GUI Event Thread
- Pate Verifier Thread

### GUI Event Thread

In a GUI there is always a GUI event thread. All all processing in responce to user mouse and tty input is run on this thread. It important to make sure that user response processing is quick and non-blocking because the GUI is not responsive until this processing finishes. Any intensive or blocking processes should be spawned on a separate thread.

The GUI event thread is part of the PySide6 Qt framework that Binary Ninja is implemented with. It is started automatically.

### PATE Verifier Thread

The `pate.PateWrapper` class is responsible for starting, stopping and I/O with the PATE verifier process. In general GUI object can only be interacted with on the GUI Event Thread. Thus this thread effects GUI changes by calling `execute_on_main_thread_and_wait`.

The thread is started in `pate.PateWrapper._run_live()` or `pate.PateWrapper._run_replay()` using `Popen()`.

### Thread Synchronization

GUI objects are NOT thread safe. Any time code running on the Pate Verifier thread need to make a change to the gui it calls `execute_on_main_thread_and_wait` to caus the code to run on the GUI Event Thread.

To synchronize user input with the verifier, a Python `threading.Condion` object is used. It is stored in `view.PateWidget.user_response_condition`. When the Pate Verifier is waiting for user input, it waits on this condition until notified by the GUI Event Thread. When the user performs some action in the GUI that is a response for the PATE Verifier it sets `view.PateWidget.user_response` to a `pate.VerifierAction` object describing the response/request. Then it calls `view.PateWidget.user_response_condition.notify` to wake up the Pate Verifier Thread that is waiting. Currently the Constrain Trace functionality does not use this mechanism. It only executes after the verifier is quiescent in which case it is safe for the GUI Event Thread to interact directly with the verifier. This was done before the `pate.VerifierAction` abstraction was implemented. Idealy the Constrain Trace functionality should be convereted.
