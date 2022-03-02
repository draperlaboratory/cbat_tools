# Organizing files (in plugins)

As far as `bapbuild` is concerned, there is one entry point into a plugin: the plugin `NAME.plugin` corresponds to the file `NAME.ml`.

Other files/modules can be organized into subfolders, or included as a library.


## Subfolders

In a folder, create a `Makefile`:

```
NAME := plugin_01
PUBLIC_NAME := my-plugin-01
PUBLIC_DESC := My hello world plugin 01

SRC := $(NAME).ml
PLUGIN := $(NAME).plugin
FLAGS := -I lib


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
        bapbuild -use-ocamlfind -package findlib.dynload $(FLAGS) $(PLUGIN)

install: build
        bapbundle update -name $(PUBLIC_NAME) $(PLUGIN)
        bapbundle update -desc "$(PUBLIC_DESC)" $(PLUGIN)
        bapbundle install $(PLUGIN)
```

Create a file called `plugin_01.ml`:

```
let () = Utils.show "Hello world, again!"
```

And in a subfolder called `lib`, create a file called `utils.ml`:

```
let show msg = Format.printf "- %s\n%!" msg
```

Here we have a `plugin_01.ml` file, which invokes a function `show` from a `Utils` module. That module is defined in `utils.ml` in a `lib` folder.

To tell `bapbuild` where to find this file, we add `-I lib` to the `bapbuild` command.

To build and install:

```
make
```

Confirm that the plugin has been installed:

```
bap list plugins
```

Uninstall and clean:

```
make uninstall clean
```


## A custom (toy) library

Create a folder called `toy_lib`, and add a file `events.ml`:

```
let report msg = Format.eprintf "[Event was logged] %s\n%!" msg
```

Add a `dune` file:

```
(library
  (name toy_lib)
  (public_name toy-lib)
  (libraries findlib.dynload))
```

Add a `toy-lib.opam` file:

```
opam-version: "2.0"
name: "toy-lib"
synopsis: "A toy library"
maintainer: "Somebody"
authors: "Somebody"
homepage: "http://somewhere.com"
bug-reports: "somebody@gmail.com"
build: [[make]]
```

And add a `Makefile`:

```
LIB := toy-lib


#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL := all

.PHONY: all
all: clean uninstall build install


#####################################################
# CLEAN
#####################################################

.PHONY: clean
clean:
        dune clean


#####################################################
# BUILD
#####################################################

build: $(LIB_SRC_FILES)
        dune build -p $(LIB) @install
        @echo "" # Force a newline in terminal output


#####################################################
# INSTALL
#####################################################

install: build
        dune install

uninstall: build
        dune uninstall
```

Build and install this toy library:

```
make
```

Confirm that `ocamlfind` sees it:

```
ocamlfind query toy-lib
```

If you would like to install it with `opam`:

```
opam install .
```

To try it out, open `utop`:

```
utop
```

Set up `topfind`:

```
#use "topfind";;
```

Import the library:

```
#require "toy-lib";;
```

Use it:

```
Toy_lib.Events.report "Hello, world!";;
```

Quit `utop`:

```
#quit
```

If you want to remove the library later, run:

```
make uninstall clean
```

If you installed it with opam, uninstall it from opam too:

```
opam remove .
```


## Include the library in a BAP plugin

In a new folder, create a file `plugin_02.ml`:

```
let () = Toy_lib.Events.report "Hello world, yet again!"
```

Add a `Makefile`:

```
NAME := plugin_02
PUBLIC_NAME := my-plugin-02
PUBLIC_DESC := My hello world plugin 02

SRC := $(NAME).ml
PLUGIN := $(NAME).plugin
PKGS := -pkgs toy-lib

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
        bapbuild $(PKGS) $(PLUGIN)

install: build
        bapbundle update -name $(PUBLIC_NAME) $(PLUGIN)
        bapbundle update -desc "$(PUBLIC_DESC)" $(PLUGIN)
        bapbundle install $(PLUGIN)
```

Note that we tell `bapbuild` to include our `toy-lib` package by adding a `-pkgs toy-lib` parameter.

Build and install the plugin (assuming `toy-lib` has been installed as was done above):

```
make
```

Confirm that the plugin is installed:

```
bap list plugins
```

Uninstall and clean:

```
make uninstall clean
```

NOTE: if you change the `toy-lib` library, you must _first_ uninstall the BAP plugin, and _then_ rebuild it. That will ensure that the new version of the `toy-lib` library will get re-packaged into the plugin.
