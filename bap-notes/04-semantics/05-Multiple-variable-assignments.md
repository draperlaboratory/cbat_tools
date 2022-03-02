# Multiple variable assignments

Sometimes a simple assignment involves setting flags too. For instance, suppose on a 32-bit architecture machine that uses status flags, we have a program that adds 0xffffffff and 0x01, and then assigns the result to the register R2:

```
mov R2, 0xffffffff + 0x01
```

What is the semantics of this program? It adds `0xffffffff` and `0x01` and assigns the result to `R2`, but it also sets the zero flag `ZF` and the overflow flag `OF`. In pseudo-core theory code:

```
(
  (set (var R2) (add (int 0xffffffff) (int 0x01)))
  (set (var ZF) (int 0x01))
  (set (var OF) (int 0x01))
)
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

Create a function that creates a binary word of a certain size:

```
let create_word (i : int) (bits : int) : Bitvec.t =
  let m = Bitvec.modulus bits in
  Bitvec.(int i mod m)
```

Create a function that adds `0xffffffff` and `0x01`, assigns the result to `R2`, sets `ZF` and `OF` to `0x01`, and then sequences those assignments into a block that ends with a fallthrough:

```
let provide_semantics (label : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let* target = T.Label.target label in
  let bits = T.Target.bits target in
  let width = T.Bitv.define bits in

  let one_bv = create_word 0x01 bits in
  let max_int_bv = create_word 0xffffffff bits in

  let one = CT.int width one_bv in
  let max_int = CT.int width max_int_bv in

  let r2 = T.Var.define width "R2" in
  let z_flag = T.Var.define width "ZF" in
  let o_flag = T.Var.define width "OF" in

  let r2_assignment = CT.set r2 (CT.add max_int one) in
  let zf_assignment = CT.set z_flag one in
  let of_assignment = CT.set o_flag one in

  let data = CT.seq r2_assignment (CT.seq zf_assignment of_assignment) in
  let ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall) in
  CT.blk label data ctrl
```

Register the function as a promise:

```
let () = KB.promise T.Semantics.slot provide_semantics
```

Add a function that creates a compilation unit:

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

Finally, generate the program and use `Toplevel.eval` to retrieve the semantics and print the result:

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

  let one_bv = create_word 0x01 bits in
  let max_int_bv = create_word 0xffffffff bits in

  let one = CT.int width one_bv in
  let max_int = CT.int width max_int_bv in

  let r2 = T.Var.define width "R2" in
  let z_flag = T.Var.define width "ZF" in
  let o_flag = T.Var.define width "OF" in

  let r2_assignment = CT.set r2 (CT.add max_int one) in
  let zf_assignment = CT.set z_flag one in
  let of_assignment = CT.set o_flag one in

  let data = CT.seq r2_assignment (CT.seq zf_assignment of_assignment) in
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
                0000000c: R2 := 0
                0000000f: ZF := 1
                00000012: OF := 1")
 (bap:insn-dests (()))
 (bap:bir (%00000009))
 (bap:bil "{
             label(%00000009)
             R2 := 0
             ZF := 1
             OF := 1
           }"))
```

Clean up:

```
make clean
```
