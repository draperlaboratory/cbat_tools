# Custom Theories

BAP's core theory language is actually a _signature_. You can add your own semantics by implementing the signature and registering it with BAP.

In your implementation, you write the methods required by the signature, but you have them return your own custom semantics.

If you register your theory with BAP, then every time that BAP disassembles a binary program, it will build your theory alongside any other registered theories. Later, when you inspect the disassembled program, you can retrieve the semantics your theory provided.

To implement your own theory, start with a module that is an instance of the `Theory.Core` signature:

```
module My_theory : Theory.Core = struct

   (* Implement the signature's methods here... *)

end
```

To make sure that all of the methods of the signature are covered, include the empty theory, which returns empty semantics for all of the methods.


```
module My_theory : Theory.Core = struct

   include Theory.Empty

   (* Implement the signature's methods here... *)

end
```

Then, implement any methods you want to provide semantics for. There are two kinds of semantics you need to provide: you need to provide the semantics of expressions (which the documentation calls "values" or "pure values"), and the semantics of statements (which the documentation calls "effects").

The general procedure is first to do this:

* Create a custom slot to hold custom semantics for expressions.
* Create another custom slot to hold custom semantics for statements.

The methods in the signature build up the semantics of each program compositionally, so they start with the smaller pieces, and then combine them into bigger and bigger pieces. So, when you implement a method in your theory, the general procedure is this:

* Fetch the semantics of the smaller pieces out of the appropriate slots
* Combine those pieces into a bigger piece of semantics
* Stash that bigger piece of semantics in the appropriate slot
* Return the semantics

The following example create a theory which provides as the "semantics" an S-expression-like string of the program. 


## A toy executable

First, create a toy executable program that we can use for the example.

In a new folder somewhere, create a sub-folder called `resources`. Inside of the `resources` folder, create an assembly file `main.asm` with the following contents:

```
    global main:function (main.end - main)

; -------------------------------------------
    section .text
; -------------------------------------------

main:
    mov rdi, 7
    add rdi, 3
    mov rax, 60
    syscall
.end:
```

In the `resources` sub-folder, add a `Makefile`:

```
SRC := main.asm
OBJ := main.o
EXE := main.elf


#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL := all
all: clean build


#####################################################
# BUILD
#####################################################

$(EXE): $(SRC)
        nasm -w+all -f elf64 -o $(OBJ) $(SRC)
        ld -e main -o $(EXE) $(OBJ)
        rm -rf $(OBJ)

build: $(EXE)


#####################################################
# CLEAN
#####################################################

.PHONY: clean
clean:
        rm -rf $(OBJ) $(EXE)
```

Build and compile:

```
make -C resources
```

Run the compiled program:

```
./resources/main.elf
```

Confirm that it returns an exit code of 10:

```
echo ${?}
```

Use `objdump` to view the program:

```
objdump -Ds resources/main.elf
```

Identify the address of the `main` function. For me, it's `0x400080`.


## The custom theory

The next task is to create a custom theory.

In the folder that is parent to the `resources` sub-folder, create a file called `custom.ml`, which the the following contents:

```
module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let
```

Add a name and a package:

```
let name = "my-theory"
let package = "my.org"
```

Add a slot to store the S-expression-like string representation that we'll build for expressions, and a slot to store the S-expression-like string representation that we'll build for statements:

```
let expr_slot : (T.Value.cls, string) KB.slot =
  KB.Class.property T.Value.cls "expr-slot" KB.Domain.string
    ~package

let stmnt_slot : (T.Semantics.cls, string) KB.slot =
  KB.Class.property T.Semantics.cls "stmnt-slot" KB.Domain.string
    ~package
``` 

Add a module that implements `T.Core`, and include the empty theory:

```
module Theory : T.Core = struct

  include T.Empty

  (* We'll implement a few methods here... *)

end
```

For convenience, define an empty effect, and an empty expression (an empty value):

```
module Theory : T.Core = struct

  ...

  let empty = T.Effect.empty T.Effect.Sort.bot
  let null_of s = T.Value.empty s

end
```

Next, implement the `int` method of the `T.Core` signature. When disassembling, BAP will call this function whenever it encounters a literal integer in an expression. 

To represent an integer, we will simply generate a string version of the binary word, and we will stash that in the expressions slot so that it can serve as the "meaning" of the expression.

```
module Theory : T.Core = struct

  ...

  let int (sort : 's T.Bitv.t T.Value.sort) (bv : Bitvec.t)
      : 's T.Bitv.t T.Value.t KB.t =
    let semantics = Format.asprintf "%a" Bitvec.pp bv in
    let snapshot = KB.Value.put expr_slot (null_of sort) semantics in
    KB.return snapshot

end
```

Next, implement the `var` method of the `T.Core` signature. When disassembling, BAP will call this function whenever it encounters a variable in an expression.

To represent a variable, we will simply use the string name of the variable, and we will stash that in the expressions slot so that it can serve as the "meaning" of the expression.

```
module Theory : T.Core = struct

  ...

  let var (var : 'a T.Var.t) : 'a T.Value.t KB.t =
    let name = T.Var.name var in
    let sort = T.Var.sort var in
    let snapshot = KB.Value.put expr_slot (null_of sort) name in
    KB.return snapshot

end
```

Next, implement the `set` method of the `T.Core` signature. When disassembling, BAP will call this function whenever it encounters a variable assignment (i.e. setting a variable to the value of an expression).

To represent a variable assignment statement as a string, we will generate a string of the form `(set VAR (EXPR))`, where we will replace `VAR` with the name of the variable, and we will replace `EXPR` with whatever S-expression-like string we have already generated for it. We will stash the resulting string in the statements slot so that it can serve as the "meaning" of the whole variable assignment statement:

```
module Theory : T.Core = struct

  ...

  let set (var : 'a T.Var.t) (expr : 'a T.Value.t KB.t)
      : T.data T.Effect.t KB.t =
    let* e = expr in
    let lhs = T.Var.name var in
    let rhs = KB.Value.get expr_slot e in
    let semantics = Format.sprintf "set %s (%s)" lhs rhs in
    let snapshot = KB.Value.put stmnt_slot empty semantics in
    KB.return snapshot

end
```

Next, implement the `blk` method of the `T.Core` signature. When disasembling, BAP will call this function whenever it encounters a block.

To represent a block, we will generate a string `(DATA) (CTRL)`, and we will replace `DATA` with whatever S-expression-like string we have already generated for the data part of the block, and we will replace `CTRL` with whatever S-expression-like string we have already generated for the control part of the block.

```
module Theory : T.Core = struct

  ...

  let blk (label : T.Label.t) (data : T.data T.Effect.t KB.t)
      (ctrl : T.ctrl T.Effect.t KB.t) : unit T.Effect.t KB.t =
    let* d = data in
    let* c = ctrl in
    let sem1 = KB.Value.get stmnt_slot d in
    let sem2 = KB.Value.get stmnt_slot c in
    let semantics = Format.sprintf "(%s) (%s)" sem1 sem2 in
    let snapshot = KB.Value.put stmnt_slot empty semantics in
    KB.return snapshot

end
```

Finally, implement the `seq` method of the `T.Core` signature. When disassmebling, BAP will call this function whenever it encounters a sequence of two statements.

To represent a sequence of two statements, we will generate a string `(STMNT1 STMNT2)`, where we replace `STMNT1` and `STMNT2` with the strings we have already generated for the two statements:

```
module Theory : T.Core = struct

  ...

  let seq (prog1 : 'a T.Effect.t KB.t) (prog2 : 'a T.Effect.t KB.t)
      : 'a T.Effect.t KB.t =
    let* p1 = prog1 in
    let* p2 = prog2 in
    let sem1 = KB.Value.get stmnt_slot p1 in
    let sem2 = KB.Value.get stmnt_slot p2 in
    let semantics = Format.sprintf "(%s %s)" sem1 sem2 in
    let snapshot = KB.Value.put stmnt_slot empty semantics in
    KB.return snapshot

end
```

There are further methods we could implement, but this is enough for an example. Any methods we did not implement are implemented by the `T.Empty` theory (which will simply return empty snapshots for anything we did not implement).

To summarize, the entire `custom.ml` file looks like this:

```
module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

open KB.Let

let name = "my-theory"
let package = "my.org"

let expr_slot : (T.Value.cls, string) KB.slot =
  KB.Class.property T.Value.cls "expr-slot" KB.Domain.string
    ~package

let stmnt_slot : (T.Semantics.cls, string) KB.slot =
  KB.Class.property T.Semantics.cls "stmnt-slot" KB.Domain.string
    ~package

module Theory : T.Core = struct

  include T.Empty

  let empty = T.Effect.empty T.Effect.Sort.bot
  let null_of s = T.Value.empty s

  let int (sort : 's T.Bitv.t T.Value.sort) (bv : Bitvec.t)
      : 's T.Bitv.t T.Value.t KB.t =
    let semantics = Format.asprintf "%a" Bitvec.pp bv in
    let snapshot = KB.Value.put expr_slot (null_of sort) semantics in
    KB.return snapshot

  let var (var : 'a T.Var.t) : 'a T.Value.t KB.t =
    let name = T.Var.name var in
    let sort = T.Var.sort var in
    let snapshot = KB.Value.put expr_slot (null_of sort) name in
    KB.return snapshot

  let set (var : 'a T.Var.t) (expr : 'a T.Value.t KB.t)
      : T.data T.Effect.t KB.t =
    let* e = expr in
    let lhs = T.Var.name var in
    let rhs = KB.Value.get expr_slot e in
    let semantics = Format.sprintf "set %s (%s)" lhs rhs in
    let snapshot = KB.Value.put stmnt_slot empty semantics in
    KB.return snapshot

  let blk (label : T.Label.t) (data : T.data T.Effect.t KB.t)
      (ctrl : T.ctrl T.Effect.t KB.t) : unit T.Effect.t KB.t =
    let* d = data in
    let* c = ctrl in
    let sem1 = KB.Value.get stmnt_slot d in
    let sem2 = KB.Value.get stmnt_slot c in
    let semantics = Format.sprintf "(%s) (%s)" sem1 sem2 in
    let snapshot = KB.Value.put stmnt_slot empty semantics in
    KB.return snapshot

  let seq (prog1 : 'a T.Effect.t KB.t) (prog2 : 'a T.Effect.t KB.t)
      : 'a T.Effect.t KB.t =
    let* p1 = prog1 in
    let* p2 = prog2 in
    let sem1 = KB.Value.get stmnt_slot p1 in
    let sem2 = KB.Value.get stmnt_slot p2 in
    let semantics = Format.sprintf "(%s %s)" sem1 sem2 in
    let snapshot = KB.Value.put stmnt_slot empty semantics in
    KB.return snapshot

end
```


## A BAP pass

The next task is to register our theory, then create a BAP pass that can inspect a label, so that we can see the semantics our theory has provided for the program. 

In the folder that is parent to the `resources` sub-folder, create a file called `kb_pass_02.ml` with these contents at the top:

```
open Core_kernel
open Bap.Std
```

Create a sub-module which contains a BAP pass that can explore the label of a particular address:

```
module Setup = struct

  module Conf = Bap_main.Extension.Configuration
  module Param_type = Bap_main.Extension.Type

  let addr = Conf.parameter Param_type.string "addr"

  let explore (addr : Bitvec.t) : unit =
    let label = T.Label.for_addr addr in
    let semantics = Toplevel.eval T.Semantics.slot label in
    Format.printf "%a\n%!" KB.Value.pp semantics

  let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
    let addr = Conf.get ctxt addr in
    let () =
      if String.is_empty addr
        then failwith "No address specified"
        else ()
    in
    let word = Bitvec.of_string addr in
    explore word

end
```

Next, create a function that registers our theory and the pass:

```
module Setup = struct

  ...

  let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
    let theory = KB.return (module Custom.Theory : T.Core) in
    T.declare theory ~package:Custom.package ~name:Custom.name;
    Project.register_pass' (pass ctxt);
    Ok ()

end
```

Finally, register the extension:

```
let () = Bap_main.Extension.declare Setup.run
```

To summarize, the whole `kb_pass_02.ml` file looks like this:

```
open Core_kernel
open Bap.Std

module T = Bap_core_theory.Theory
module KB = Bap_core_theory.KB

module Setup = struct

  module Conf = Bap_main.Extension.Configuration
  module Param_type = Bap_main.Extension.Type

  let addr = Conf.parameter Param_type.string "addr"

  let explore (addr : Bitvec.t) : unit =
    let label = T.Label.for_addr addr in
    let semantics = Toplevel.eval T.Semantics.slot label in
    Format.printf "%a\n%!" KB.Value.pp semantics

  let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
    let addr = Conf.get ctxt addr in
    let () =
      if String.is_empty addr
        then failwith "No address specified"
        else ()
    in
    let word = Bitvec.of_string addr in
    explore word

  let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
    let theory = KB.return (module Custom.Theory : T.Core) in
    T.declare theory ~package:Custom.package ~name:Custom.name;
    Project.register_pass' (pass ctxt);
    Ok ()

end

let () = Bap_main.Extension.declare Setup.run
```

Add a `Makefile`:

```
PUBLIC_NAME := my-kb-pass-02
PUBLIC_DESC := My demo KB pass 02

NAME := kb_pass_02
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

Confirm that the plugin (which is named `my-kb-pass-02`) is installed:

```
bap list plugins
```

Now run the pass over the toy executable, providing the address of the `main` function as the `addr` argument:

```
bap resources/main.elf --my-kb-pass-02 --my-kb-pass-02-addr 0x400080
```

It should print out a fair amount of information about the program at that location, something like this:

```
((bap:ir-graph "0000001f:
                00000020: RDI := 7")
 (bap:insn-dests (()))
 (bap:insn-ops ((EDI 7)))
 (bap:insn-asm "movl $0x7, %edi")
 ...
```

If you do not see `((my.org:stmnt-slot ...` in the output, clean the cache:

```
bap cache --clean
```

Then try again:

```
bap resources/main.elf --my-kb-pass-02 --my-kb-pass-02-addr 0x400080
```

This time, you should see something about `my.org:stmnt-slot` in the output:

```
((my.org:stmnt-slot "((set RDI (0x7)) () () ())")
 (bap:ir-graph "0000001f:
                00000020: RDI := 7")
 (bap:insn-dests (()))
 (bap:insn-ops ((EDI 7)))
 (bap:insn-asm "movl $0x7, %edi")
 ...
```

Notice the "semantics" that our custom theory has provided:

```
((set RDI (0x7)) () () ())
```

We can see that our theory has generated an S-expression-like string that expresses the "meaning" of the program at this particular program label. (The empty parantheses are there because we did not implement all of the methods in the `Theory.Core` signature.)

Clean up:

```
make uninstall
make clean
```

Clean up the toy executable in the `resources` sub-folder too if you like:

```
make clean -C resources
```

## Other examples

For a fuller example, see the [BIL plugin semantics](https://github.com/BinaryAnalysisPlatform/bap/blob/master/plugins/bil/bil_semantics.ml). It constructs BIL expressions and puts them in [Exp.slot](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Exp/index.html#val-slot), and it constructs BIL statement lists and puts them in the [Bil.slot](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Bil/index.html#val-slot).


## Documentation

For the full `Theory.Core` signature and all of the methods you can implement, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-core-theory/Bap_core_theory/Theory/module-type-Core/index.html).
