# Using Toplevel.eval

`Toplevel.eval` can be used to get the data held in a particular slot of a particular object.


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

Add a function that creates a new car object and gives it a color:

```
let provide_color : Car.tag KB.obj KB.t =
  let* car = KB.Object.create Car.cls in
  let* () = KB.provide Car.color car "red" in
  KB.return car
```

Next, use `Toplevel.eval` to extract the color:

```
let () =
  let color = Toplevel.eval Car.color provide_color in
  Format.printf "- Color: %s\n%!" color
```

To summarize, the entire `main.ml` file looks like this:

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

let provide_color : Car.tag KB.obj KB.t =
  let* car = KB.Object.create Car.cls in
  let* () = KB.provide Car.color car "red" in
  KB.return car

let () =
  let color = Toplevel.eval Car.color provide_color in
  Format.printf "- Color: %s\n%!" color
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
- Color: blue
```

Clean up:

```
make clean
```

## Documentation

For more on Toplevel eval, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Toplevel/index.html).
