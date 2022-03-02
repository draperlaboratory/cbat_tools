# A more complex analysis plugin

Here is an example of a slightly more complex KB analysis plugin.


## Example

In a new folder somewhere, create a folder called `project_analysis_02.ml` with the following code at the top of the file:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

module A = Project.Analysis
```

Provide a name, package, description, and grammar for a command:

```
let name = "encoding"
let package = "my.org"
let desc = "prints the encoding of a given address"
let grammar = A.(args @@ program $ flag "show-name")
```

Note that the grammar says that the command takes a `program` argument (i.e., a program label), and a flag `show-name`. 

Create a function that takes a program label, and a boolean flag. Have it retrieve the encoding of the given label, and if the flag is specified, have it also print the name of the program label (if it has a name). 

```
let show_encoding (label : T.Label.t) (show_name : bool) : unit KB.t =
  let* encoding = KB.collect T.Label.encoding label in
  Format.printf "Encoding: %s\n%!" (T.Language.to_string encoding);
  if show_name then
    let* name = KB.collect T.Label.name label in
    let repr = Option.value name ~default:"none" in
    Format.printf "Name: %s\n%!" repr;
    KB.return ()
  else
    KB.return ()
```

Finally, register the command:

```
let () =
  A.register name grammar show_encoding
    ~desc
    ~package
```

To summarize, the entire `project_analysis_02.ml` file looks like this:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

module A = Project.Analysis

let name = "encoding"
let package = "my.org"
let desc = "prints the encoding of a given address"
let grammar = A.(args @@ program $ flag "show-name")

let show_encoding (label : T.Label.t) (show_name : bool) : unit KB.t =
  let* encoding = KB.collect T.Label.encoding label in
  Format.printf "Encoding: %s\n%!" (T.Language.to_string encoding);
  if show_name then
    let* name = KB.collect T.Label.name label in
    let repr = Option.value name ~default:"none" in
    Format.printf "Name: %s\n%!" repr;
    KB.return ()
  else
    KB.return ()

let () = 
  A.register name grammar show_encoding
    ~desc
    ~package
```

Add a `Makefile`:

```
PUBLIC_NAME := my-project-analysis-02
PUBLIC_DESC := My project analysis 02

NAME := project_analysis_02
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

Save a project, e.g.:

```
bap /bin/true --project test.proj --update
```

Start the analysis REPL for that project:

```
bap analyze --project test.proj
```

List the installed commands:

```
bap> commands
```

You should see your `my.org:encoding` command in the list:

```
my.org:encoding                          prints the encoding of a given address
bap:subroutines                          prints all subroutines
bap:units                                prints all units
bap:subroutine                           prints a subroutine
bap:instructions                         prints all instructions
bap:instruction                          prints the instruction semantics
```

List the compilation units:

```
bap> bap:units
```

It should print something like this:

```
file:/bin/true                           bap:amd64
```

List the instructions for the compilation unit:

```
bap> bap:instructions /bin/true
```

It should list all of the instruction labels:

```
...
/bin/true:0x17da
/bin/true:__libc_start_main
/bin/true:0x17d4
/bin/true:0x17cd
/bin/true:0x17c6
/bin/true:0x17bf
/bin/true:0x17be
...
```

Run your `encoding` command on, say, the `__libc_start_main` label:

```
bap> my.org:encoding /bin/true:__libc_start_main
```

It should print out the encoding, e.g.:

```
Encoding: bap:llvm-x86_64
```

Note that it did not print out the name of the label. This is because we ran the command without adding the `:show-name` flag. 

Run it with the `:show-name` flag:

```
bap> my.org:encoding /bin/true:__libc_start_main :show-name
```

Now it prints the name of the label in addition to the encoding:

```
Encoding: bap:llvm-x86_64
Name: __libc_start_main
```

Try running it on a label that doesn't have a name, e.g.:

```
bap> my.org:encoding /bin/true:0x1d47 :show-name
```

This prints the encoding of the label, and provides no name as expected:

```
Encoding: bap:llvm-x86_64
Name: none
```

Exit the REPL:

```
bap> quit
```

Clean up:

```
make uninstall clean
```
