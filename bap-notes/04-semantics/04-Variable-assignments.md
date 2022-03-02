# Variable assignments

As an example of a very simple program, consider one that moves, say, the integer 3 into a register R2 (in pseudo-assembly):

```
mov R2, 0x03
```

What is the semantics of this program? The semantics is what it "does" when executed, and in this case, it simply assigns the value `0x03` to a variable `R2`. In pseudo-core theory:

```
(set (var R2) (int 0x03))
```  


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

Add a function that creates a binary word of a certain size:

```
let create_word (i : int) (bits : int) : Bitvec.t =
  let m = Bitvec.modulus bits in
  Bitvec.(int i mod m)
```

Start a function to create the semantics for a label:

```
let create_semantics (label : T.Label.t) : 'a T.effect KB.t =
  (* We'll build the core-theory program here *)
```

Get an instance of the core theory module:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
```

Define a bitvector type with the target's word size, and create a binary word with that width to represent `0x03`:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits
```

Create a core theory integer with that value:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits
  let value = CT.int width word in
```

Create a core theory variable `R2`:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits
  let value = CT.int width word in
  let var = CT.var width "R2" in
```

Now assign the value to the variable:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits
  let value = CT.int width word in
  let var = CT.var width "R2" in
  let data = CT.set var value in
```

Add a fallthrough:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits
  let value = CT.int width word in
  let var = CT.var width "R2" in
  let data = CT.set var value in
  let ctrl = KB.return (T.Effect.empty T.EFfect.Sort.fall) in
```

Finally, create a core theory block:

```
let create_semantics (label : T.Label.t) (bits : int) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits
  let value = CT.int width word in
  let var = CT.var width "R2" in
  let data = CT.set var value in
  let ctrl = KB.return (T.Effect.empty T.EFfect.Sort.fall) in
  CT.blk label data ctrl
```

Register the function as a promise:

```
let () = KB.promise T.Semantics.slot provide_semantics
```

Next, add a function that creates a compilation unit:

```
let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit
```

Add a function that creates a program label and adds a compilation unit to it:

```
let create_program (addr : Bitvec.t) (target : T.Target.t) : T.Label.t KB.t =
  let* label = T.Label.for_addr addr in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  KB.return label
```

Now, generate the program, and use `Toplevel.eval` to retrieve the semantics and print the result:

```
let () =
  let target = T.Target.read "bap:armv7+le" in
  let addr = Bitvec.(int 0x10400 mod m32) in
  let label = create_program addr target in
  let program = Toplevel.eval T.Semantics.slot label in
  Format.printf "%a\n%!" KB.Value.pp program
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

let create_word (i : int) (bits : int) : Bitvec.t =
  let m = Bitvec.modulus bits in
  Bitvec.(int i mod m)

let provide_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in
  let word = create_word 0x03 bits in
  let value = CT.int width word in
  let var = T.Var.define width "R2" in
  let data = CT.set var value in
  let ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall) in
  CT.blk label data ctrl

let () = KB.promise T.Semantics.slot provide_semantics

let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit

let create_program (addr : Bitvec.t) (target : T.Target.t) : T.Label.t KB.t =
  let* label = T.Label.for_addr addr in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  KB.return label

let () =
  let target = T.Target.read "bap:armv7+le" in
  let addr = Bitvec.(int 0x10400 mod m32) in
  let label = create_program addr target in
  let program = Toplevel.eval T.Semantics.slot label in
  Format.printf "%a\n%!" KB.Value.pp program
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
((bap:ir-graph "00000009:
                0000000c: R2 := 3")
 (bap:insn-dests (()))
 (bap:bir (%00000009))
 (bap:bil "{
             label(%00000009)
             R2 := 3
           }"))
```

Clean up:

```
make clean
```
