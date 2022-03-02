# Passes

A pass is an analysis of a program that you can trigger from the command line.

In a new folder, create a file `pass_00.ml`, with a function that can process a BAP project:

```
open Bap.Std

let pass (proj : Project.t) : unit =
  print_endline "Running my pass: hello, world!"
```

Next, define an extension, and have the extension register the pass:

```
let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' pass;
  Ok ()
```

Note the tick-mark on `Project.register_pass'`. That registers a pass that returns `unit`. 

Finally, declare the extension:

```
let () = Bap_main.Extension.declare run
```

The whole `pass_00.ml` file looks like this:

```
open Bap.Std

let pass (proj : Project.t) : unit =
  print_endline "Running my pass: hello, world!"

let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' pass;
  Ok ()

let () = Bap_main.Extension.declare run
```

Create a `Makefile`:

```
PUBLIC_NAME := my-pass-00
PUBLIC_DESC := My demo pass 00

NAME := pass_00
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

Build and install the plugin:

```
make
```

Confirm that the plugin is installed:

```
bap list plugins
```

Now run the pass over some binary executable, e.g.:

```
bap /bin/true --my-pass-00
```

The pass is triggered by the `--my-pass-00` flag. If you omit the flag, BAP will not run your pass. For instance, no message will be printed out if you run this:

```
bap /bin/true
```

Clean up:

```
make uninstall 
make clean
```
