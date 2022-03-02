# Extension errors

The signature of an extension function is this:

```
Bap_main.ctxt -> (unit, Bap_main.error) Stdlib.result
```

Note:
* It takes one argument, namely a context that BAP passes it when it executes the extension.
* It returns a status: either `unit` if all is okay, or a `Bap_main.error`.

The `Bap_main.error` is an alias for `Bap_main.Extension.Error.t`, which is an extensible type. You can define your own constructors for it.

In a new folder, create a file `extension_01.ml`, and add a `Fail` constructor:

```
type Bap_main.Extension.Error.t += Fail of string
```

Now we can invoke `Fail "some message"` to create a new `Bap_main.error`. 

Next, add a custom error-printer function:

```
let print_error (e : Bap_main.Extension.Error.t) : string option =
  match e with
  | Fail s -> Some (Format.sprintf "We encountered an error: %s" s)
  | _ -> None
```

Add an extension function that returns a `Fail` error:

```
let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Error (Fail "could not initialize extension")
```

Finally, register the custom printer, and declare the extension:

```
let () =
  Bap_main.Extension.Error.register_printer print_error;
  Bap_main.Extension.declare run
```

The entire `extension_01.ml` file now looks like this:

```
type Bap_main.Extension.Error.t += Fail of string

let print_error (e : Bap_main.Extension.Error.t) : string option =
  match e with
  | Fail s -> Some (Format.sprintf "We encountered an error: %s" s)
  | _ -> None

let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Error (Fail "could not initialize extension")

let () =
  Bap_main.Extension.Error.register_printer print_error;
  Bap_main.Extension.declare run
```

Create a `Makefile`:

```
PUBLIC_NAME := my-extension-01
PUBLIC_DESC := My demo extension 01

NAME := extension_01
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

Run BAP, e.g.:

```
bap /bin/true
```

BAP will print the custom error message, and exit.

Uninstall and clean:

```
make uninstall clean
```

