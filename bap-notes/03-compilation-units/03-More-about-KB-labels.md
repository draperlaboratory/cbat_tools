# More about KB labels

A label has a variety of slots that can hold information. For instance, there are slots for:

* An address
* A name (e.g., a symbol name)
* Etc


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

Add a procedure that creates a program object (a label) and then adds an address in the `addr` slot:

```
let create_program (addr : Bitvec.t) : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  let* () = KB.provide T.Label.addr label (Some addr) in
  KB.return label
```

Add a function that prints an address:

```
let inspect_address (addr : Bitvec.t option) : unit =
  match addr with
  | Some addr -> Format.printf "Address: %a\n%!" Bitvec.pp addr
  | None -> Format.printf "Address: None\n%!"
```

Now create an address and a program:

```
let () =
  let addr = Bitvec.(int 0x10400 mod m32) in
  let program = create_program addr in
```

Then use `KB.run` to evaluate the program, and inspect the address:

```
let () =
  ...
  let state = Toplevel.current () in
  let result = KB.run T.Program.cls program state in
  match result with
  | Ok (snapshot, _) ->
    begin
      let addr = KB.Value.get T.Label.addr snapshot in
      inspect_address addr
    end
  | Error e -> Format.eprintf "Error: %a\n%!" KB.Conflict.pp e
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

let create_program (addr : Bitvec.t) : T.Label.t KB.t =
  let* label = KB.Object.create T.Program.cls in
  let* () = KB.provide T.Label.addr label (Some addr) in
  KB.return label

let inspect_address (addr : Bitvec.t option) : unit =
  match addr with
  | Some addr -> Format.printf "Address: %a\n%!" Bitvec.pp addr
  | None -> Format.printf "Address: None\n%!"

let () =
  let addr = Bitvec.(int 0x10400 mod m32) in
  let program = create_program addr in

  let state = Toplevel.current () in
  let result = KB.run T.Program.cls program state in
  match result with
  | Ok (snapshot, _) ->
    begin
      let addr = KB.Value.get T.Label.addr snapshot in
      inspect_address addr
    end
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

It will print out the the address:

```
Address: 0x10400
```

Clean up:

```
make clean
```


## Documentation

For more information about other slots associated with labels, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-core-theory/Bap_core_theory/Theory/Label/index.html).
