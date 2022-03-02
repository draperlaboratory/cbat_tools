# Targets

A compilation unit object has a slot that can hold a target architecture. Once you retrieve a target, you can retrieve various features:

* The endianness
* The word size (in bits)
* The size of addresses
* The size of instructions
* The size of instruction alignment
* Which register is the stack pointer
* A list of registers
* Etc


## Retrieving targets

To find out which targets your local copy of BAP supports, use `bap list`:

```
bap list targets
```

That will provide a list of target names. To programmatically retrieve a target by its name, use `Theory.Target.read`, e.g.:

```
let target = Theory.Target.read "bap:armv7+le"
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

Add a function that takes a `T.Target.t` and then prints some of its features:

```
let inspect_target (target : T.Target.t) : unit =
  let endianness = T.Target.endianness target in
  let wordsize = T.Target.bits target in
  let memory_address_size = T.Target.data_addr_size target in
  let pc_size = T.Target.code_addr_size target in
  let insn_alignment_size = T.Target.code_alignment target in
  let mem_var = T.Target.data target in
  let sp = T.Target.reg target T.Role.Register.stack_pointer in
  let sp_to_string sp =
    match sp with
    | Some reg -> T.Var.name reg
    | None -> "unknown"
  in
  let regs = T.Target.regs target in
  let regs_to_string regs = 
    let regs_list = List.map (Set.to_list regs) ~f:T.Var.name in
    String.concat regs_list ~sep:", "
  in
  Format.printf "- Endianness: %a\n%!" T.Endianness.pp endianness;
  Format.printf "- Wordsize: %d\n%!" wordsize;
  Format.printf "- Memory address size: %d\n%!" memory_address_size;
  Format.printf "- Instruction size (program counter size): %d\n%!" pc_size;
  Format.printf "- Instruction alignment: %d\n%!" insn_alignment_size;
  Format.printf "- Memory variable (its name): %s\n%!" (T.Var.name mem_var);
  Format.printf "- SP: %s\n%!" (sp_to_string sp);
  Format.printf "- Registers: %s\n%!" (regs_to_string regs)
```

Add a function that takes a `T.Unit.t option` and then uses `KB.run` to take a snapshot and inspect the target:

```
let inspect_comp_unit (comp_unit : T.Unit.t option) (state : KB.state) : unit =
  match comp_unit with
  | Some comp_unit' ->
    begin
      let result = KB.run T.Unit.cls (KB.return comp_unit') state in
      match result with
      | Ok (snapshot, _) ->
        let target = KB.Value.get T.Unit.target snapshot in
        Format.printf "- Target: %a\n%!" T.Target.pp target;
        inspect_target target
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

let inspect_target (target : T.Target.t) : unit =
  let endianness = T.Target.endianness target in
  let wordsize = T.Target.bits target in
  let memory_address_size = T.Target.data_addr_size target in
  let pc_size = T.Target.code_addr_size target in
  let insn_alignment_size = T.Target.code_alignment target in
  let mem_var = T.Target.data target in
  let sp = T.Target.reg target T.Role.Register.stack_pointer in
  let sp_to_string sp =
    match sp with
    | Some reg -> T.Var.name reg
    | None -> "unknown"
  in
  let regs = T.Target.regs target in
  let regs_to_string regs = 
    let regs_list = List.map (Set.to_list regs) ~f:T.Var.name in
    String.concat regs_list ~sep:", "
  in
  Format.printf "- Endianness: %a\n%!" T.Endianness.pp endianness;
  Format.printf "- Wordsize: %d\n%!" wordsize;
  Format.printf "- Memory address size: %d\n%!" memory_address_size;
  Format.printf "- Instruction size (program counter size): %d\n%!" pc_size;
  Format.printf "- Instruction alignment: %d\n%!" insn_alignment_size;
  Format.printf "- Memory variable (its name): %s\n%!" (T.Var.name mem_var);
  Format.printf "- SP: %s\n%!" (sp_to_string sp);
  Format.printf "- Registers: %s\n%!" (regs_to_string regs)

let inspect_comp_unit (comp_unit : T.Unit.t option) (state : KB.state) : unit =
  match comp_unit with
  | Some comp_unit' ->
    begin
      let result = KB.run T.Unit.cls (KB.return comp_unit') state in
      match result with
      | Ok (snapshot, _) ->
        let target = KB.Value.get T.Unit.target snapshot in
        Format.printf "- Target: %a\n%!" T.Target.pp target;
        inspect_target target
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

It will print out:

```
- Target: bap:armv7+le
- Endianness: core:le
- Wordsize: 32
- Memory address size: 32
- Instruction size (program counter size): 32
- Instruction alignment: 32
- Memory variable (its name): mem
- SP: SP
- Registers: CF, LR, NF, QF, R0, R1, R10, R11, R12, R2, R3, R4, R5, R6, R7, R8, R9, SP, VF, ZF
```

Clean up:

```
make clean
```


## Other ways to get the target

If you have a label, there is a shortcut to get the target:

```
let* target = Theory.Label.target label in
...
```

From a pass, you can use `Project.target`:

```
let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
  let target = Project.target proj in
  ...
```


## Documentation

To see more options, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-core-theory/Bap_core_theory/Theory/Target/index.html).
