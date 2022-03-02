# Promises

You can use `KB.provide` to fill a slot with data. If you want to defer providing that data until the slot is actually accessed, you can instead use `KB.promise` to register a function that will compute the value at call time.


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

Define a function that takes an object of the car class, and provides a color:

```
let provide_color (_ : Car.tag KB.obj) : string KB.t =
  Kb.return "red"
```

Now, use `KB.promise` to register that function:

```
let () =
  KB.promise Car.color provide_color;
```

Now, create a car object, and retrieve its color:

```
let () =
  KB.promise Car.color provide_color;
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in
      let* color = KB.collect Car.color car in
      Format.printf "- Color: %s\n%!" color;
      KB.return ()
    end
```

When the color is collected, the `provide_color` function is triggered, which in turn returns the color.

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

let provide_color (_ : Car.tag KB.obj) : string KB.t =
  Kb.return "red"

let () =
  KB.promise Car.color provide_color;
  Toplevel.exec
    begin
      let* car = KB.Object.create Car.cls in
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

It will print the color:

```
- Color: red
```

Clean up:

```
make clean
```