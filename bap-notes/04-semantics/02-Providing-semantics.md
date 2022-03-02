# Providing Semantics

The simplest core theory program is a block. Blocks contain two parts:

* A data part
* A control part

The data part contains variable assignments. In other words, this part of the block only has data effects, i.e., it updates the values of variables.

The control part contains instructions that have control effects, i.e., instructions which change the control flow of the program, e.g., gotos and jumps.

The simplest block is an empty block (it has an empty data part, and an empty control part). This is basically just a fallthrough.


## Example

In a new folder somewhere, create a file called `main.ml` with the following:

```
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

Start a function to create the semantics for a label:

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  (* We'll build an empty block here *)
```

Get an instance of the core theory module:

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
```

Define a nop as a type of data effect:

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let nop = T.Effect.Sort.data "NOP" in
```

Create a data part that's just a nop:

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let nop = T.Effect.Sort.data "NOP" in
  let data = KB.return (T.Effect.empty nop) in
```

Create an empty control part (a fallthrough):

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let nop = T.Effect.Sort.data "NOP" in
  let data = KB.return (T.Effect.empty nop) in
  let ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall) in
```

Finally, create a core theory block from the specified data and control parts:

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let nop = T.Effect.Sort.data "NOP" in
  let data = KB.return (T.Effect.empty nop) in
  let ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall) in
  CT.blk label data ctrl
```

Next, add a function that creates a compilation unit:

```
let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit
```

Create a function that creates a program label and adds a compilation unit and semantics to it:

```
let create_program (addr : Bitvec.t) (target : T.Target.t) : T.Label.t KB.t =
  let* label = T.Label.for_addr addr in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  let* semantics = create_semantics label in
  let* () = KB.provide T.Semantics.slot label semantics in
  KB.return label
```

Create a function that takes a snapshot of a program label and prints the result:

```
let inspect_program (label : T.Label.t KB.t) (state : KB.state) : unit =
  let result = KB.run T.Program.cls label state in
  match result with
  | Ok (snapshot, _) -> Format.printf "%a\n%!" KB.Value.pp snapshot
  | Error e -> Format.printf "%a\n%!" KB.Conflict.pp e
```

Finally, trigger the whole thing:

```
let () =
  let state = Toplevel.current () in
  let target = T.Target.read "bap:armv7+le" in
  let addr = Bitvec.(int 0x10400 mod m32) in
  let label = create_program addr target in
  inspect_program label state
```

To summarize, the entire `main.ml` file looks like this:

```
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"

let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let nop = T.Effect.Sort.data "NOP" in
  let data = KB.return (T.Effect.empty nop) in
  let ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall) in
  CT.blk label data ctrl

let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit

let create_program (addr : Bitvec.t) (target : T.Target.t) : T.Label.t KB.t =
  let* label = T.Label.for_addr addr in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  let* semantics = create_semantics label in
  let* () = KB.provide T.Semantics.slot label semantics in
  KB.return label

let inspect_program (label : T.Label.t KB.t) (state : KB.state) : unit =
  let result = KB.run T.Program.cls label state in
  match result with
  | Ok (snapshot, _) -> Format.printf "%a\n%!" KB.Value.pp snapshot
  | Error e -> Format.printf "%a\n%!" KB.Conflict.pp e

let () =
  let state = Toplevel.current () in
  let target = T.Target.read "bap:armv7+le" in
  let addr = Bitvec.(int 0x10400 mod m32) in
  let label = create_program addr target in
  inspect_program label state
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

It will print out the snapshot:

```
((bap:arch armv7)    
 (core:semantics
  ((bap:ir-graph "00000009:
                  ")
   (bap:insn-dests (()))
   (bap:bil "{
               label(%00000009)
             }")))
 (core:label-addr (0x10400))
 (core:label-unit (2))
 (core:encoding bap:llvm-armv7))
```

Clean up:

```
make clean
```


## Documentation

For more details about core theory programs, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-core-theory/Bap_core_theory/Theory/module-type-Core/index.html).
