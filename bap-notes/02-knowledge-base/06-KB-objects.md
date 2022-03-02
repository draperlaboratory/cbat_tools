# Creating and updating KB objects

KB objects are created with `KB.Object.create`. Data can be put in their slots with `KB.provide`, and data can be retrieved from the slots with `KB.collect`.


## Example

In a new folder somewhere, create a file called `main.ml` that has a class to represent cars:

```
open Core_kernel
open Bap.Std

module KB = Bap_knowledge.Knowledge
open KB.Let

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"

module Car = struct

  let package = "my.org"
  type tag = Car
  type sort = unit

  let name = "car"
  let desc = "A class representing cars"
  let index = ()
  let cls : (tag, sort) Kb.cls =
    KB.Class.declare name index ~package ~desc

  let string_domain : string KB.Domain.t =
    KB.Class.flat "string-domain"
      ~inspect:(fun s -> Sexp.Atom s)
      ~equal:String.(=)
      ~empty:""

  let color : (tag, string) KB.slot =
    KB.Class.property cls "color" string_domain ~package

end
```

If we want to create and manipulate objects in the KB, we need to run a KB computation.

One simple way to do this is by using `Bap.Std.Toplevel.exec`:

```
let () =
  Toplevel.exec
    begin

      (* Create and manipulate KB objects...*)

      KB.return ()
    end
```

First, create an instance of the car class:

```
let () =
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in

      KB.return ()
    end
```

Get a string representation of the object and print it:

```
let () =
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in
      let* repr = KB.Object.repr Car.cls in
      Format.printf "- Car: %s\n%!" repr;

      KB.return ()
    end
```

Put the color "red" in the `Car.color` slot:

```
let () =
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in
      let* repr = KB.Object.repr Car.cls in
      Format.printf "- Car: %s\n%!" repr;

      let* () = KB.provide Car.color car "red" in

      KB.return ()
    end
```

Collect the value in the slot and print it:

```
let () =
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in
      let* repr = KB.Object.repr Car.cls in
      Format.printf "- Car: %s\n%!" repr;

      let* () = KB.provide Car.color car "red" in
      let* color = KB.collect Car.color car in
      Format.printf "- Color: %s\n%!" color;

      KB.return ()
    end
```

To summarize, the entire `main.ml` file looks like this:

```
open Core_kernel
open Bap.Std

module KB = Bap_knowledge.Knowledge

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"

module Car = struct

  let package = "my.org"
  type tag = Car
  type sort = unit

  let name = "car"
  let desc = "A class representing cars"
  let index = ()
  let cls : (tag, sort) Kb.cls =
    KB.Class.declare name index ~package ~desc

  let string_domain : string KB.Domain.t =
    KB.Class.flat "string-domain"
      ~inspect:(fun s -> Sexp.Atom s)
      ~equal:String.(=)
      ~empty:""

  let color : (tag, string) KB.slot =
    KB.Class.property cls "color" string_domain ~package

end

let () =
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in
      let* repr = KB.Object.repr Car.cls in
      Format.printf "- Car: %s\n%!" repr;

      let* () = KB.provide Car.color car "red" in
      let* color = KB.collect Car.color car in
      Format.printf "- Color: %s\n%!" color;

      KB.return ()
    end
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

It will print out something that looks like this:

```
- Car: #<my.org:car <0x2>>
- Color: red
```

Clean up:

```
make clean
```
