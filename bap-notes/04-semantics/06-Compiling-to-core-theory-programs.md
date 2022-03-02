# "Compiling" to core theory programs

Core theory programs can be used to provide semantics for a custom assembly-like language.

In this example, we will:

* Write a program in a toy assembly-like language.
* Read it in and construct a simple AST.
* Walk the AST and create core theory semantics for the program. 


## Example

In a new folder somewhere, create a file `program.lisp` with the following contents:

```
(block foo
  (data (
    (set r0 (int 0x3))
    (set r1 (reg r0))))
  (control
    (goto bar)))

(block bar
  (data (
    (set r2 (add (int 0x7) (reg r3)))
    (set r0 (reg r2))))
  (control
    (goto foo)))
```

This program has two blocks (labeled `foo` and `bar`). Each block has a `data` section (with variable assignments), and a `control` section (with `goto`s). 

Create a file `ast.ml` with the following types:

```
open Core_kernel

type label = string
type reg = string
type num = int

type expr = Var of reg | Num of num | Add of expr * expr
type assignment = Assign of reg * expr

type data = assignment list
type control = Goto of label | Fallthrough

type block = Block of label * data * control
type t = block list
```

Add some accessor functions:

```
let lhs_of_assignment a = match a with Assign (reg, _) -> reg
let rhs_of_assignment a = match a with Assign (_, expr) -> expr

let label_of_block b = match b with Block (label, _, _) -> label
let data_of_block b = match b with Block (_, data, _) -> data
let control_of_block b = match b with Block (_, _, control) -> control
```

Add a convenience function to generate error messages:

```
let err (msg : string) (sexp : Sexp.t) : string =
  let sexp_str = Sexp.to_string sexp in
  Format.sprintf "Parse error: %s: %s" msg sexp_str
```

Add a function to convert a string to an integer:

```
let parse_number (num : string) : num =
  try int_of_string num
  with _ -> failwith (err "Invalid number" (Sexp.Atom num))
```

Add a function to recursively parse an expression (variables, integers, and additions):

```
let rec parse_expr (sexp : Sexp.t) : expr =
  match sexp with
  | Sexp.List [ Atom "reg"; Atom reg ] -> Var reg
  | Sexp.List [ Atom "int"; Atom n ] -> Num (parse_number n)
  | Sexp.List [ Atom "add"; e1 ; e2 ] ->
    Add (parse_expr e1, parse_expr e2)
  | _ -> failwith (err "Invalid expr" sexp)
```

Add a function to parse the data assignments:

```
let parse_data (sexps : Sexp.t list) : data =
  List.fold sexps ~init:[] ~f:(fun assigns sexp -> match sexp with
    | Sexp.List [ Atom "set"; Atom reg; e ] ->
      List.append assigns [Assign (reg, parse_expr e)]
    | _ -> failwith (err "Invalid data" sexp))
```

Add a function to parse the control section:

```
let parse_ctrl (sexp : Sexp.t) : control =
  match sexp with
  | Sexp.List [ Atom "goto"; Atom label ] -> Goto label
  | Sexp.List [ Atom "fallthrough" ] -> Fallthrough
  | _ -> failwith (err "Invalid control" sexp)
```

Add a function to start parsing:

```
let parse (sexps : Sexp.t list) : t =
  List.fold sexps ~init:[] ~f:(fun blks sexp -> match sexp with
    | Sexp.List [ Atom "block"; Atom label;
        List [ Atom "data"; List data ];
        List [ Atom "control"; ctrl ]; ] ->
      List.append blks [Block (label, parse_data data, parse_ctrl ctrl)]
    | _ -> failwith (err "Parse error" sexp))
```

Add a function to read a program from a file:

```
et from_file (filepath : string) : t =
  let sexps = Sexp.load_sexps filepath in
  parse sexps
```

To summarize, the entire `ast.ml` file looks like this:

```
open Core_kernel

type label = string
type reg = string
type num = int

type expr = Var of reg | Num of num | Add of expr * expr
type assignment = Assign of reg * expr

type data = assignment list
type control = Goto of label | Fallthrough

type block = Block of label * data * control
type t = block list

let lhs_of_assignment a = match a with Assign (reg, _) -> reg
let rhs_of_assignment a = match a with Assign (_, expr) -> expr

let label_of_block b = match b with Block (label, _, _) -> label
let data_of_block b = match b with Block (_, data, _) -> data
let control_of_block b = match b with Block (_, _, control) -> control

let err (msg : string) (sexp : Sexp.t) : string =
  let sexp_str = Sexp.to_string sexp in
  Format.sprintf "Parse error: %s: %s" msg sexp_str

let parse_number (num : string) : num =
  try int_of_string num
  with _ -> failwith (err "Invalid number" (Sexp.Atom num))

let rec parse_expr (sexp : Sexp.t) : expr =
  match sexp with
  | Sexp.List [ Atom "reg"; Atom reg ] -> Var reg
  | Sexp.List [ Atom "int"; Atom n ] -> Num (parse_number n)
  | Sexp.List [ Atom "add"; e1 ; e2 ] ->
    Add (parse_expr e1, parse_expr e2)
  | _ -> failwith (err "Invalid expr" sexp)

let parse_data (sexps : Sexp.t list) : data =
  List.fold sexps ~init:[] ~f:(fun assigns sexp -> match sexp with
    | Sexp.List [ Atom "set"; Atom reg; e ] ->
      List.append assigns [Assign (reg, parse_expr e)]
    | _ -> failwith (err "Invalid data" sexp))

let parse_ctrl (sexp : Sexp.t) : control =
  match sexp with
  | Sexp.List [ Atom "goto"; Atom label ] -> Goto label
  | Sexp.List [ Atom "fallthrough" ] -> Fallthrough
  | _ -> failwith (err "Invalid control" sexp)

let parse (sexps : Sexp.t list) : t =
  List.fold sexps ~init:[] ~f:(fun blks sexp -> match sexp with
    | Sexp.List [ Atom "block"; Atom label;
        List [ Atom "data"; List data ];
        List [ Atom "control"; ctrl ]; ] ->
      List.append blks [Block (label, parse_data data, parse_ctrl ctrl)]
    | _ -> failwith (err "Parse error" sexp))

let from_file (filepath : string) : t =
  let sexps = Sexp.load_sexps filepath in
  parse sexps
```

Next, create a file `compiler.mli` with the following interface:

```
module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

module Make(CT : T.Core) : sig
  val semantics_of : Ast.t -> unit T.effect KB.t
end
```

Create a file called `compiler.ml` with the following:

```
open Core_kernel

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let
```

Add a module parameterized by the `Core` theory module:

```
module Make(CT : T.Core) = struct

  (* We'll "compile" the semantics here... *)

end
```

Add the following declarations:

```
module Make(CT : T.Core) = struct

  let m = Bitvec.modulus 32
  let width = T.Bitv.define 32
  let nop = T.Effect.Sort.data "NOP"
  let no_data = KB.return (T.Effect.empty nop)
  let no_ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall)
  let empty_blk = CT.blk T.Label.null no_data no_ctrl

end
```

Add a function to generate semantics for expressions:

```
module Make(CT : T.Core) = struct

  ...

  let rec compile_expr (expr : Ast.expr) : 'b T.Bitv.t T.value KB.t =
    match expr with
    | Ast.Var reg -> CT.var (T.Var.define width reg)
    | Ast.Num n -> CT.int width Bitvec.(int n mod m)
    | Ast.Add (e1, e2) -> CT.add (compile_expr e1) (compile_expr e2)

end
```

Add a function to generate semantics for assignments:

```
module Make(CT : T.Core) = struct

  ...

  let compile_assignment (assign : Ast.assignment) : 'a T.effect KB.t =
    let reg = Ast.lhs_of_assignment assign in
    let var = T.Var.define width reg in
    let expr = Ast.rhs_of_assignment assign in
    CT.set var (compile_expr expr)

end
```

Add a function to fold the assignments into a single data section, and a function to generate semantics for the control section:

```
module Make(CT : T.Core) = struct

  ...

  let compile_data (data : Ast.data) : 'a T.effect KB.t =
    List.fold data ~init:no_data ~f:(fun acc assignment ->
      CT.seq (compile_assignment assignment) acc)

  let compile_ctrl (ctrl : Ast.control) : 'a T.effect KB.t =
    match ctrl with
    | Goto dest ->
      let* label = T.Label.for_name dest in
      CT.goto label
    | Fallthrough -> no_ctrl

end
```

Add a function to generate the semantics for blocks:

```
module Make(CT : T.Core) = struct

  ...

  let compile_blk (blk : Ast.block) : 'a T.effect KB.t =
    let blk_name = Ast.label_of_block blk in
    let* label = T.Label.for_name blk_name in
    let assignments = Ast.data_of_block blk in
    let* data = compile_data assignments in
    let control = Ast.control_of_block blk in
    let* ctrl = compile_ctrl control in
    CT.blk label (KB.return data) (KB.return ctrl)

end
```

Finally, add a function to get the semantics from an AST:

```
module Make(CT : T.Core) = struct

  ...

  let semantics_of (ast : Ast.t) : 'a T.effect KB.t =
    List.fold ast ~init:empty_blk ~f:(fun acc blk ->
      CT.seq (compile_blk blk) acc)

end
```

To summarize the "compiler," the entire `compiler.ml` file looks like this:

```
open Core_kernel

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

module Make(CT : T.Core) = struct

  let m = Bitvec.modulus 32
  let width = T.Bitv.define 32
  let nop = T.Effect.Sort.data "NOP"
  let no_data = KB.return (T.Effect.empty nop)
  let no_ctrl = KB.return (T.Effect.empty T.Effect.Sort.fall)
  let empty_blk = CT.blk T.Label.null no_data no_ctrl

  let rec compile_expr (expr : Ast.expr) : 'b T.Bitv.t T.value KB.t =
    match expr with
    | Ast.Var reg -> CT.var (T.Var.define width reg)
    | Ast.Num n -> CT.int width Bitvec.(int n mod m)
    | Ast.Add (e1, e2) -> CT.add (compile_expr e1) (compile_expr e2)

  let compile_assignment (assign : Ast.assignment) : 'a T.effect KB.t =
    let reg = Ast.lhs_of_assignment assign in
    let var = T.Var.define width reg in
    let expr = Ast.rhs_of_assignment assign in
    CT.set var (compile_expr expr)

  let compile_data (data : Ast.data) : 'a T.effect KB.t =
    List.fold data ~init:no_data ~f:(fun acc assignment ->
      CT.seq (compile_assignment assignment) acc)

  let compile_ctrl (ctrl : Ast.control) : 'a T.effect KB.t =
    match ctrl with
    | Goto dest ->
      let* label = T.Label.for_name dest in
      CT.goto label
    | Fallthrough -> no_ctrl

  let compile_blk (blk : Ast.block) : 'a T.effect KB.t =
    let blk_name = Ast.label_of_block blk in
    let* label = T.Label.for_name blk_name in
    let assignments = Ast.data_of_block blk in
    let* data = compile_data assignments in
    let control = Ast.control_of_block blk in
    let* ctrl = compile_ctrl control in
    CT.blk label (KB.return data) (KB.return ctrl)

  let semantics_of (ast : Ast.t) : 'a T.effect KB.t =
    List.fold ast ~init:empty_blk ~f:(fun acc blk ->
      CT.seq (compile_blk blk) acc)

end
```

Create a file `main.ml` with the following contents:

```
pen Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

Add a function that uses the compiler to generate semantics:

```
let provide_semantics (ast : Ast.t) (_ : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let module Cmplr = Compiler.Make(CT) in
  Cmplr.semantics_of ast
```

Get the AST and register the promise:

```
let () =
  let ast = Ast.from_file "program.lisp" in
  KB.promise T.Semantics.slot (provide_semantics ast)
```

Finally, generate the program, retrieve its semantics, and print the result:

```
let () =
  let label = KB.Object.create T.Program.cls in
  let program = Toplevel.eval T.Semantics.slot label in
  Format.printf "%a\n%!" KB.Value.pp program
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

let provide_semantics (ast : Ast.t) (_ : T.Label.t) : 'a T.effect KB.t =
  let* (module CT) = T.current in
  let module Cmplr = Compiler.Make(CT) in
  Cmplr.semantics_of ast

let () =
  let ast = Ast.from_file "program.lisp" in
  KB.promise T.Semantics.slot (provide_semantics ast)

let () =
  let label = KB.Object.create T.Program.cls in
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
((bap:ir-graph       
  "0000000a:
   0000000e: r0 := r2
   00000012: r2 := 7 + r3
   00000015: goto @foo
   0000001f: goto @foo
   00000013:
   00000019: r1 := r0
   0000001c: r0 := 3
   0000001e: goto @bar")
 (bap:insn-dests ((10 19)))
 (bap:bir (@bar @foo))
 (bap:bil
  "{
     label(%0000000a)
     r0 := r2
     r2 := 7 + r3
     call(foo)
     label(%00000013)
     r1 := r0
     r0 := 3
     call(bar)
   }"))
```

Clean up:

```
make clean
```
