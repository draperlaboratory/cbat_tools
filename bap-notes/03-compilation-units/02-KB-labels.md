# KB Labels

A "label" represents a location in a program. It represents the program that begins at that particular point in the executable.

In the KB, labels are objects that belong to the `Program` class. In other words, a label is the object BAP uses to represent a program.

Hence, these types are aliases:

```
Theory.Label.t
Theory.program KB.obj
```


## Example

In a new folder somewhere, create a file called `main.ml` with the following:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

Add a procedure that creates a program object (a label):

```
let create_program : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  KB.return label
```

This will create an empty program, whose slots are empty and ready to be filled by further information. At this point, let's just use `KB.run` to execute this procedure and inspect the snapshot it returns:

```
let () =
  let state = Toplevel.current () in
  let result = KB.run T.Program.cls create_program state in
  match result with
  | Ok (snapshot, _) -> Format.printf "Program: %a\n%!" KB.Value.pp snapshot
  | Error e -> Format.eprintf "KB error: %a\n%!" KB.Conflict.pp e
```

To summarize, the entire `main.ml` file looks like this:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"

let create_program : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  KB.return label

let () =
  let state = Toplevel.current () in
  let result = KB.run T.Program.cls create_program state in
  match result with
  | Ok (snapshot, _) -> Format.printf "Program: %a\n%!" KB.Value.pp snapshot
  | Error e -> Format.eprintf "Error: %a\n%!" KB.Conflict.pp e
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
        dune exec ./$(EXE)
```

Run the program:

```
make
```

It will print out the snapshot (just an empty program):

```
Program: ()
```

Clean up:

```
make clean
```
