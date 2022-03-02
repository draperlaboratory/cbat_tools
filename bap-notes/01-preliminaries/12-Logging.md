# Logging

In your plugins, you can send debug- and info-level messages to BAP's log stream, and they will be printed to the default BAP log, which is located at:

```
${XDG_STATE_HOME}/bap/log
```

E.g., on Ubuntu:

```
~/.local/state/bap/log
```

To see debug-level messages, you must run your plugin with the environment variable `BAP_DEBUG` set to `1`.


## Example

In a new folder, create a file called `pass_03.ml` and instantiate the BAP log:

```
open Core_kernel
open Bap.Std

module L = Bap_main_event.Log.Create()
```

Add a pass that sends a message to the info channel and the debug channel:

```
let pass (proj : Project.t) : unit =
  L.info "My pass 03 is: %s" "running";
  L.debug "Debug: %s" "a debug message"
```

Create an extension that registers the pass:

```
let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' pass;
  Ok ()
```

And finally, declare the extension:

```
let () =
  Bap_main.Extension.declare run
```

So the whole file looks like this:

```
open Core_kernel
open Bap.Std

module L = Bap_main_event.Log.Create()

let pass (proj : Project.t) : unit =
  L.info "My pass 03 is: %s" "running";
  L.debug "Debug: %s" "a debug message"

let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' pass;
  Ok ()

let () =
  Bap_main.Extension.declare run
```

Add a `Makefile`:

```
PUBLIC_NAME := my-pass-03
PUBLIC_DESC := My demo pass 03

NAME := pass_03
SRC := $(NAME).ml
PLUGIN := $(NAME).plugin


#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL := all

all: clean uninstall install


#####################################################
# THE PLUGIN
#####################################################

.PHONY: clean
clean:
        bapbuild -clean

uninstall:
        bapbundle remove $(PLUGIN)

build: $(SRC)
        bapbuild -use-ocamlfind -package findlib.dynload $(PLUGIN)

install: build
        bapbundle update -name $(PUBLIC_NAME) $(PLUGIN)
        bapbundle update -desc "$(PUBLIC_DESC)" $(PLUGIN)
        bapbundle install $(PLUGIN)
```

Build and install:

```
make
```

Run the pass:

```
bap /bin/true --my-pass-03
```

Look at the last few lines of the BAP log:

```
tail -n3 ~/.local/state/bap/log
```

The last line should be:

```
my-pass-03.info> My pass 03 is: running
```

Notice that the debug message is not present. To see it, run `bap` while `BAP_DEBUG=1` is set:

```
BAP_DEBUG=1 bap /bin/true --my-pass-03
```

Tail the log again:

```
tail -n3 ~/.local/state/bap/log
```

The last two lines should be:

```
my-pass-03.info> My pass 03 is: running
my-pass-03.debug> Debug: a debug message
```

Clean up:

```
make uninstall clean
```
