# Using BAP as a library

BAP can be used as a library. Before calling any code from the library, first call `Bap_main.init ()` to initialize the library, otherwise undefined behavior could (silently) occur.


## Example

In a new folder somewhere, create a file called `main.ml`, with these declarations at the top:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
```

Call `Bap_main.init`:

```
let () = match Bap_main.init () with
  | Ok () -> ()
  | Error e ->
    failwith (Format.asprintf "%a" Bap_main.Extension.Error.pp e)
```

Add a function to load a binary program:

```
let load_exe (filename : string) : project =
  let input = Project.Input.file ~loader:"llvm" ~filename in
  match Project.create input ~package:filename with
  | Ok proj -> proj
  | Error e -> failwith (Error.to_string_hum e)
```

Finally, get the filepath to an executable from `argv`, load the program, and print the target architecture:

```
let () =
  let filepath =
    if Array.length Sys.argv <= 1 then
      failwith "Argument missing: specify a /path/to/exe"
    else
      Sys.argv.(1)
  in
  Format.printf "Loading: %s\n%!" filepath;
  let project = load_exe filepath in
  let target = Project.target project in
  Format.printf "Target architecture: %a\n%!" T.Target.pp target
```

To summarize, the entire `main.ml` file looks like this:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error e ->
    failwith (Format.asprintf "%a" Bap_main.Extension.Error.pp e)

let load_exe (filename : string) : project =
  let input = Project.Input.file ~loader:"llvm" ~filename in
  match Project.create input ~package:filename with
  | Ok proj -> proj
  | Error e -> failwith (Error.to_string_hum e)

let () =
  let filepath =
    if Array.length Sys.argv <= 1 then
      failwith "Argument missing: specify a /path/to/exe"
    else
      Sys.argv.(1)
  in
  Format.printf "Loading: %s\n%!" filepath;
  let project = load_exe filepath in
  let target = Project.target project in
  Format.printf "Target architecture: %a\n%!" T.Target.pp target
```

Add a `dune` file:

```
(executable
  (name main)
  (libraries findlib.dynload bap))
```

Add a `Makefile`:

```
EXE := main.exe


#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL := all

all: clean run


#####################################################
# THE EXE
#####################################################

.PHONY: clean
clean:
        dune clean

build:
        dune build ./$(EXE)

run: build
        dune exec ./$(EXE) -- /bin/true
```

Build the program:

```
make build
```

Run it on, say, `/bin/true`:

```
dune exec ./main.exe -- /bin/true
```

It will print the target architecture, e.g.:

```
Loading: /bin/true   
Target architecture: bap:amd64
```

Clean up:

```
make clean
```

## Documentation

The above example does not handle any caching. For a more sophisticated example, see the [disassemble plugin](https://github.com/BinaryAnalysisPlatform/bap/blob/master/plugins/disassemble/disassemble_main.ml). For more about using BAP as a library, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html). 
