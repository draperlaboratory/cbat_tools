# KB Slots

Every KB slot has the following type:

```
('k, 'p) KB.slot
```

Note that:
* `'k` is the tag that uniquely identifies a class, i.e., the `'k` in the class's type `('k, 's) Kb.cls`.
* `'p` is the type of data that goes in the slot, e.g. `string`, `int option`, etc.


## Example

In a new folder somewhere, create a file called `main.ml` with the following:

```
open Core_kernel

module KB = Bap_knowledge.Knowledge

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

Add a class to represent cars:

```
module Car = struct

  let package = "my.org"
  type tag = Car
  type sort = unit

  let name = "car"
  let desc = "A class representing cars"
  let index = ()
  let cls : (tag, sort) Kb.cls =
    KB.Class.declare name index ~package ~desc

end
```

Add a string domain:

```
module Car = struct

  ...

  let string_domain : string KB.Domain.t =
    KB.Class.flat "string-domain"
      ~inspect:(fun s -> Sexp.Atom s)
      ~equal:String.(=)
      ~empty:""

end
```

Declare a slot to hold the color:

```
module Car = struct

  ...

  let color : (tag, string) KB.slot =
    KB.Class.property cls "color" string_domain ~package

end
```

At this point, we have created a car class, whose objects will have one slot that can be filled with the name of a color (a string).

We aren't doing anything with this class yet, so let's just print out the name of the class.

```
let get_name (cls : ('k, 's) KB.cls) : string =
  let kb_name = KB.Class.name cls in
  KB.Name.show kb_name

let () =
  let name = get_name Car.cls in
  Format.printf "Car class name: %s\n%!" name
```

To summarize, the entire `main.ml` file looks like this:

```
open Core_kernel

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

let get_name (cls : ('k, 's) KB.cls) : string =
  let kb_name = KB.Class.name cls in
  KB.Name.show kb_name

let () =
  let name = get_name Car.cls in
  Format.printf "Car class name: %s\n%!" name
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

It will print out the name of the class:

```
Car class name: my.org:car
```

Clean up:

```
make clean
```
