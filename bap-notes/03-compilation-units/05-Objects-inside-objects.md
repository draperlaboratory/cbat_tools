# Extracting an object from inside another object

A compilation unit is a KB object (with its own set of slots), and it lives in the slot of a label, which is a parent object.

If we take a snapshot of the parent object (the label), and then we look in the compilation unit slot, we will find a compilation unit object.

If we want to inspect that object, we need to take a snapshot of it (so taking a snapshot of a parent object does not take a snapshot of children objects).


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

Add functions to create a label, a compilation unit, and a program:

```
let create_label (addr : Bitvec.t) : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  let* () = KB.provide T.Label.addr label (Some addr) in
  KB.return label

let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit

let create_program (addr : Bitvec.t) (target : T.Target.t) : T.Label.t KB.t =
  let* label = create_label addr in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  KB.return label
```

Add a function that takes a `T.Unit.t option` and then uses `KB.run` to take a snapshot:

```
let inspect_comp_unit (comp_unit : T.Unit.t option) (state : KB.state) : unit =
  match comp_unit with
  | Some comp_unit' ->
    begin
      let result = KB.run T.Unit.cls (KB.return comp_unit') state in
      match result with
      | Ok (snapshot, _) ->
        let target = KB.Value.get T.Unit.target snapshot in
        Format.printf "- Target: %a\n%!" T.Target.pp target
      | Error e -> Format.printf "Error: %a\n%!" KB.Conflict.pp e
    end
  | None -> Format.printf "No compilation unit\n%!"
```

Add a function that takes a program label and then uses `KB.run` to take a snapshot:

```
let inspect_program (program : T.Label.t KB.t) (state : KB.state) : unit =
  let result = KB.run T.Program.cls program state in
  match result with
  | Ok (snapshot, state') ->
    begin
      let comp_unit = KB.Value.get T.Label.unit snapshot in
      inspect_comp_unit comp_unit state'
    end
  | Error e -> Format.printf "Error: %a\n%!" KB.Conflict.pp e
```

Note that the above retrieves the compilation unit object from the `T.Label.unit` slot in the snapshot, and then it applies `inspect_comp_unit` to it.

Finally, create a program, and then inspect it:

```
let () =
  let target = T.Target.read "bap:armv7+le" in
  let addr = Bitvec.(int 0x10400 mod m32) in
  let program = create_program addr target in
  
  let state = Toplevel.current () in
  inspect_program program state
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

let create_label (addr : Bitvec.t) : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  let* () = KB.provide T.Label.addr label (Some addr) in
  KB.return label

let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit

let create_program (addr : Bitvec.t) (target : T.Target.t) : T.Label.t KB.t =
  let* label = create_label addr in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in

  KB.return label

let inspect_comp_unit (comp_unit : T.Unit.t option) (state : KB.state) : unit =
  match comp_unit with
  | Some comp_unit' ->
    begin
      let result = KB.run T.Unit.cls (KB.return comp_unit') state in
      match result with
      | Ok (snapshot, _) ->
        let target = KB.Value.get T.Unit.target snapshot in
        Format.printf "- Target: %a\n%!" T.Target.pp target
      | Error e -> Format.printf "Error: %a\n%!" KB.Conflict.pp e
    end
  | None -> Format.printf "No compilation unit\n%!"

let inspect_program (program : T.Label.t KB.t) (state : KB.state) : unit =
  let result = KB.run T.Program.cls program state in
  match result with
  | Ok (snapshot, state') ->
    begin
      let comp_unit = KB.Value.get T.Label.unit snapshot in
      inspect_comp_unit comp_unit state'
    end
  | Error e -> Format.printf "Error: %a\n%!" KB.Conflict.pp e

let () =
  let target = T.Target.read "bap:armv7+le" in
  let addr = Bitvec.(int 0x10400 mod m32) in
  let program = create_program addr target in
  
  let state = Toplevel.current () in
  inspect_program program state
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

It will print out the target:

```
- Target: bap:armv7+le
```

Clean up:

```
make clean
```
