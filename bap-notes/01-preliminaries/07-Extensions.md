# BAP Extensions

Use `Bap_main.Extension.declare` to declare your own custom extensions to BAP. 

In a new folder, create a file `extension_00.ml`. In it, create a function that will run your own extension code, e.g.: 

```
let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  print_endline "My extension runs";
  Ok ()
```

Next, declare the function as an extension of BAP:

```
let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  print_endline "My extension runs";
  Ok ()

let () = Bap_main.Extension.declare run
```

This tells BAP that the `run` function is an extension that it should execute whenever it runs.

Create a `Makefile`:

```
PUBLIC_NAME := my-extension-00
PUBLIC_DESC := My demo extension 00

NAME := extension_00
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

Confirm that your plugin is installed:

```
bap list plugins
```

Run `bap`, e.g.:

```
bap /bin/true
```

BAP will print `My extension runs`, which confirms that it executed the extension.

Uninstall and clean:

```
make uninstall clean
```

