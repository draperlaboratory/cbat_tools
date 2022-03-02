# A simple analysis plugin

Here is an example of how to build and register a custom KB analysis.


## Example

In a new folder somewhere, create a folder called `project_analysis_01.ml` with the following code at the top of the file:

```
open Bap.Std

module KB = Bap_core_theory.KB
module A = Project.Analysis
```

Provide a name, package, and description for a command:

```
let name = "hello-world"
let package = "my.org"
let desc = "prints 'hello world'"
```

Add a "grammar" of command line arguments that the command accepts:

```
let grammar = A.(args empty)
```

This grammar says that the command takes only an empty argument.

Now that we have specified a name for the command a grammar, we need to implement it. To do that, we need to create a function that takes an empty argument (unit), and returns `unit KB.t`. We'll just have it print "hello world":

```
let do_hello_world () : unit KB.t =        
  print_endline "Hello world";
  KB.return ()
```

Note: the arguments that this function accepts need to correspond exactly to the grammar specified. In this case, the grammar `A.(args empty)` says the command just takes an empty argument, and so the function here also accepts an empty argument (a thunk).

Now that we have specifed a name and a grammar for the command, and written a function to implement the command, let's register the command:

```
let () =
  A.register name grammar do_hello_world
    ~desc
    ~package
```

To summarize, the entire `project_analysis_01.ml` file looks like this:

```
open Bap.Std

module KB = Bap_core_theory.KB
module A = Project.Analysis

let name = "hello-world"
let package = "my.org"
let desc = "prints 'hello world'"
let grammar = A.(args empty)

let do_hello_world () : unit KB.t =
  print_endline "Hello world";
  KB.return ()

let () =
  A.register name grammar do_hello_world
    ~desc
    ~package
```

Add a `Makefile`:

```
PUBLIC_NAME := my-project-analysis-01
PUBLIC_DESC := My project analysis 01

NAME := project_analysis_01
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

Start the analysis REPL:

```
bap analyze
```

List the installed commands:

```
bap> commands
```

You should see your `my.org:hello-world` command in the list:

```
bap:subroutines                          prints all subroutines
my.org:hello-world                       prints 'hello world'
bap:units                                prints all units
bap:subroutine                           prints a subroutine
bap:instructions                         prints all instructions
bap:instruction                          prints the instruction semantics
```

Try running it:

```
bap> my.org:hello-world
```

It prints the expected result:

```
Hello world
```

Quit the REPL:

```
bap> quit
```

Clean up:

```
make uninstall clean
```
