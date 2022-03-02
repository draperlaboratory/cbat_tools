# Retrieving a label

When BAP disassembles a binary program, it fills the slots for each label as best as it can.

You can take a snapshot of any program label, if you know its address.


## A toy executable

First, create a toy executable program that we can use for the example.

In a new folder somewhere, create a sub-folder called `resources`. Inside of the `resources` folder, create an assembly file `main.asm` with the following contents:

```
    global main:function (main.end - main)

; -------------------------------------------
    section .text
; -------------------------------------------

main:
    mov rdi, 3
    mov rax, 60
    syscall
.end:
```

This program will simply exit with an exit code of 3.

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

Confirm that it returns an exit code of 3:

```
echo ${?}
```

Use `objdump` to view the program:

```
objdump -Ds resources/main.elf
```

Identify the address of the `main` function. For me, it's `0x400080`.


## A BAP pass

The next task is to create a BAP pass that can inspect a label. 

In the folder that is parent to the `resources` sub-folder, create a file called `kb_pass_01.ml` with these contents at the top:

```
open Core_kernel
open Bap.Std
```

Create a sub-module:

```
module Analysis = struct

  module T = Bap_core_theory.Theory
  module KB = Bap_core_theory.KB
  open KB.Let

  (* We'll add code to inspect the label here ... *)

end
```

Add a function that retrieves the label for a given address:

```
module Analysis = struct

  ...

  let get_label (addr : Bitvec.t) : T.Label.t KB.t =
    let* label = T.Label.for_addr addr in
    KB.return label

end
```

And add a function that takes a snapshot of a label and prints the result:

```
module Analysis = struct

  ...

  let explore (addr : Bitvec.t) : unit =
    let label = get_label addr in
    let state = Toplevel.current () in
    let result = KB.run T.Program.cls label state in
    match result with
    | Ok (snapshot, _) ->
      begin
        Format.printf "Program: %a\n%!" KB.Value.pp snapshot
      end
    | Error e -> Format.printf "KB error: %a\n%!" KB.Conflict.pp e

end
```

Create another sub-module:

```
module Setup = struct

  module Conf = Bap_main.Extension.Configuration
  module Param_type = Bap_main.Extension.Type

  (* We'll set up the BAP pass here... *)

end
```

Define a command line parameter that takes an address (as a string):

```
module Setup = struct

  ...

  let addr = Conf.parameter Param_type.string "addr"

end
```

Add a pass which runs `Analysis.explore` on the provided address (provided the address is not empty):

```
module Setup = struct

  ...

  let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
    let addr = Conf.get ctxt addr in
    let () =
      if String.is_empty addr
        then failwith "No address specified"
        else ()
    in
    let word = Bitvec.of_string addr in
    Analysis.explore word

end
```

Add a function that registers the pass:

```
module Setup = struct

  ...

  let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
    Project.register_pass' (pass ctxt);
    Ok ()

end
```

Finally, declare `run` as an extension:

```
let () = Bap_main.Extension.declare Setup.run
```

To summarize, the whole `kb_pass_01.ml` file looks like this:

```
open Core_kernel
open Bap.Std

module Analysis = struct

  module T = Bap_core_theory.Theory
  module KB = Bap_core_theory.KB
  open KB.Let

  let get_label (addr : Bitvec.t) : T.Label.t KB.t =
    let* label = T.Label.for_addr addr in
    KB.return label

  let explore (addr : Bitvec.t) : unit =
    let label = get_label addr in
    let state = Toplevel.current () in
    let result = KB.run T.Program.cls label state in
    match result with
    | Ok (snapshot, _) ->
      begin
        Format.printf "Program: %a\n%!" KB.Value.pp snapshot
      end
    | Error e -> Format.printf "KB error: %a\n%!" KB.Conflict.pp e

end

module Setup = struct

  module Conf = Bap_main.Extension.Configuration
  module Param_type = Bap_main.Extension.Type

  let addr = Conf.parameter Param_type.string "addr"

  let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
    let addr = Conf.get ctxt addr in
    let () =
      if String.is_empty addr
        then failwith "No address specified"
        else ()
    in
    let word = Bitvec.of_string addr in
    Analysis.explore word

  let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
    Project.register_pass' (pass ctxt);
    Ok ()

end

let () = Bap_main.Extension.declare Setup.run
```

Add a `Makefile`:

```
PUBLIC_NAME := my-kb-pass-01
PUBLIC_DESC := My demo KB pass 01

NAME := kb_pass_01
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

Confirm that the plugin (which is named `my-kb-pass-01`) is installed:

```
bap list plugins
```

Now run the pass over the toy executable, providing the address of the `main` function as the `addr` argument:

```
bap resources/main.elf --my-kb-pass-01 --my-kb-pass-01-addr 0x400080
```

It should print out a fair amount of information about the program at that location:

```
Program: ((bap:lisp-args
           ((((lisp-symbol (EDI)) (bap:exp EDI))
             ((bap:static-value (0x3)) (bap:exp 3)))))
          (bap:lisp-name (llvm-x86_64:MOV32ri))
          (bap:insn ((MOV32ri EDI 0x3)))
          (bap:mem ("400080: bf 03 00 00 00"))
          ...
```

Try to run it with an address that does not exist in the binary, e.g.:

```
bap resources/main.elf --my-kb-pass-01 --my-kb-pass-01-addr 0x555555
```

It will print out nothing but an address:

```
Program: ((core:label-addr (0x555555)))
```

This is because there is no program information about this program label, since the label does not exist in the binary.

Clean up:

```
make uninstall
make clean
```

Clean up the toy executable in the `resources` sub-folder too if you like:

```
make clean -C resources
```
