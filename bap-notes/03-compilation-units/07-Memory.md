# Memory

A program label can have a chunk of memory associated with it. This is stored in the label's memory slot.


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

Add a function to get the endianness:

```
let get_endianness (target : T.Target.t) : endian =
  let endianness = T.Target.endianness target in
  if T.Endianness.(equal endianness le)
    then LittleEndian
    else BigEndian
```

Add a function to create a blank (zeroed-out) chunk of memory:

```
let create_mem (addr : Word.t) (size : int) (target : T.Target.t) : Memory.t =
  let endianness = get_endianness target in
  let addr_size = T.Target.data_addr_size target in
  let num_bytes = size * (addr_size / 8) in
  let bytes = Bytes.init num_bytes ~f:(fun _ -> '\x00') in
  let data = Bigstring.of_bytes bytes in
  let result = Memory.create endianness addr data in
  match result with
  | Ok mem -> mem
  | _ -> failwith "Failed to create memory"
```

Add a function to create a label, with a chunk of memory:

```
let create_label (addr : Word.t) (target : T.Target.t) (mem_size : int)
    : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  let addr_bv = Word.to_bitvec addr in
  let* () = KB.provide T.Label.addr label (Some addr_bv) in
  let mem = create_mem addr mem_size target in
  let* () = KB.provide Memory.slot label (Some mem) in
  KB.return label
```

Add a function to create a compilation unit:

```
let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit
```

Add a functon to create a program:

```
let create_program (addr : Word.t) (target : T.Target.t) (mem_size : int)
    : T.Label.t KB.t =
  let* label = create_label addr target mem_size in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  KB.return label
```

Add a function to take a snapshot and inspect the result:

```
let inspect_program (program : T.Label.t KB.t) (state : KB.state) : unit =
  let result = KB.run T.Program.cls program state in
  match result with
  | Ok (snapshot, _) -> Format.printf "Program: %a\n%!" KB.Value.pp snapshot
  | Error e -> Format.printf "Error: %a\n%!" KB.Conflict.pp e
```

Finally, create the program and trigger the snapshot:

```
let () =
  let target = T.Target.read "bap:armv7+le" in
  let addr = Word.of_int 0x10400 ~width:(T.Target.bits target) in
  let mem_size = 16 in
  let program = create_program addr target mem_size in

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

let get_endianness (target : T.Target.t) : endian =
  let endianness = T.Target.endianness target in
  if T.Endianness.(equal endianness le)
    then LittleEndian
    else BigEndian

let create_mem (addr : Word.t) (size : int) (target : T.Target.t) : Memory.t =
  let endianness = get_endianness target in
  let addr_size = T.Target.data_addr_size target in
  let num_bytes = size * (addr_size / 8) in
  let bytes = Bytes.init num_bytes ~f:(fun _ -> '\x00') in
  let data = Bigstring.of_bytes bytes in
  let result = Memory.create endianness addr data in
  match result with
  | Ok mem -> mem
  | _ -> failwith "Failed to create memory"

let create_label (addr : Word.t) (target : T.Target.t) (mem_size : int)
    : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  let addr_bv = Word.to_bitvec addr in
  let* () = KB.provide T.Label.addr label (Some addr_bv) in
  let mem = create_mem addr mem_size target in
  let* () = KB.provide Memory.slot label (Some mem) in
  KB.return label

let create_compilation_unit (target : T.Target.t) : T.Unit.t KB.t =
  let* comp_unit = KB.Object.create T.Unit.cls in
  let* () = KB.provide T.Unit.target comp_unit target in
  KB.return comp_unit

let create_program (addr : Word.t) (target : T.Target.t) (mem_size : int)
    : T.Label.t KB.t =
  let* label = create_label addr target mem_size in
  let* comp_unit = create_compilation_unit target in
  let* () = KB.provide T.Label.unit label (Some comp_unit) in
  KB.return label

let inspect_program (program : T.Label.t KB.t) (state : KB.state) : unit =
  let result = KB.run T.Program.cls program state in
  match result with
  | Ok (snapshot, _) -> Format.printf "Program: %a\n%!" KB.Value.pp snapshot
  | Error e -> Format.printf "Error: %a\n%!" KB.Conflict.pp e

let () =
  let target = T.Target.read "bap:armv7+le" in
  let addr = Word.of_int 0x10400 ~width:(T.Target.bits target) in
  let mem_size = 16 in
  let program = create_program addr target mem_size in

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

It will print out:

```
Program: ((bap:mem   
           ("00010400  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
             |................|
             00010410  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
             |................|
             00010420  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
             |................|
             00010430  00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
             |................|"))
          (bap:arch armv7)
          (core:semantics
           ((core:insn-code
             ("00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
               00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
               00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
               00"))))
          (core:label-addr (0x10400))
          (core:label-unit (2))
          (core:encoding bap:llvm-armv7))
```

Clean up:

```
make clean
```
