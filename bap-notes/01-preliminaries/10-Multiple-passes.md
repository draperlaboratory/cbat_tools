# Multiple Passes


## Passes that return `unit`

Suppose you have a pass:

```
let pass (proj : Project.t) : unit =
  print_endline "Running my pass: hello, world!"
```

Note that this pass returns `unit`. To register it, we declare an extension, and declare it with the `Project.register_pass'` function (note the tick mark): 

```
let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' pass;
  Ok ()
```

## Passes that return updated projects

Suppose instead that you want to write a pass that alters the project somehow, and you want to return the altered version of the project so that other passes can use it. We can register that sort of pass with `Project.register_pass` (note the absense of a tick mark).

In a new folder, create a file `pass_01.ml`, with a function that takes a BAP project and returns a new, updated project:

```
open Bap.Std

let pass (proj : Project.t) : Project.t =
  print_endline "Running my pass: hello, world!"
  (* do something to update the project *)
  (* now return the project *)
  proj
```

Next, define an extension, and have the extension register the pass:

```
let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass pass;
  Ok ()
```

Note that we use `Project.register_pass` instead of `Project.register_pass'` to register this pass. 

Finally, declare the extension:

```
let () = Bap_main.Extension.declare run
```

The whole `pass_01.ml` file looks like this:

```
open Bap.Std

let pass (proj : Project.t) : Project.t =
  print_endline "Running my pass: hello, world!"
  (* do something to update the project *)
  (* now return the project *)
  proj

let run (_ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass pass;
  Ok ()

let () = Bap_main.Extension.declare run
```

Create a `Makefile`:

```
PUBLIC_NAME := my-pass-01
PUBLIC_DESC := My demo pass 01

NAME := pass_01
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
bap /bin/true --my-pass-01
```

When this pass runs, it returns an updated version of the project, which BAP an pass on to other passes.

Clean up:

```
make uninstall 
make clean
```


## Running multiple passes

You can build and install many passes, and tell BAP to run any of them together
in a chain, one after the other.

For example, if you were to create another pass and give the plugin the public name `my-pass-02`, then after you install it, you can tell BAP to run `my-pass-00`, then `my-pass-01`, then `my-pass-02`, one after the other:

```
bap /bin/true --my-pass-00 --my-pass-01 --my-pass-02
```

That will first run `my-pass-00`, then `my-pass-01`, then `my-pass-02`. And, since `my-pass-01` returns an updated project, BAP will take the version of the project that `my-pass-01` produces, and feed it into `my-pass-02` as its input. 

Note that if you switch the order of the arguments in the above command, BAP will execute the passes in the order you list them:

```
bap /bin/true --my-pass-01 --my-pass-00 --my-pass-02
```


## Suppressing a pass

You can suppress a pass by prefixing `--no-` to it. For instance, to tell BAP _not_ to run `my-pass-00`:

```
bap /bin/true --no-my-pass-00 --my-pass-01 --my-pass-02
```

