# Snapshots (KB values)

You can take a snapshot of an object. A snapshot is just a record of the values contained in the object's slots at the time the snapshot is taken.

In BAP's documentation, a snapshot is called a "value," but bear in mind that a KB-value is not just a single value. It is an array of values, taken from the slots of the object at the time the snapshot was taken.


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
let build_car : Car.tag KB.obj KB.t =
  let* car = KB.Object.create Car.cls in
  let* () = KB.provide Car.color car "red" in
  KB.return car
```

Next, use `KB.run` to execute the `build_car` procedure:

```
let () =
  let state = Toplevel.current () in
  let result = KB.run Car.cls build_car state in
```

If the KB computation succeeds, it returns a pair `(snapshot, new_state)`, where `snapshot` is a snapshot of the object at the end of the computation, and `new_state` is the updated KB state. If the computation fails, it returns a KB error. We can print both of them:

```
let () =
  let state = Toplevel.current () in
  let result = KB.run Car.cls build_car state in
  match result with
  | Ok (snapshot, _) -> Format.printf "- Snapshot: %a\n%!" KB.Value.pp snapshot
  | Error e -> Format.eprintf "KB problem: %a\n%!" KB.Conflict.pp e
```

We can pull out the data from the `color` slot, and print that too:

```
let () =
  let state = Toplevel.current () in
  let result = KB.run Car.cls build_car state in
  match result with
  | Ok (snapshot, _) ->
    begin
      Format.printf "- Snapshot: %a\n%!" KB.Value.pp snapshot;
      let color = KB.Value.get Car.color snapshot in
      Format.printf "- Color: %s\n%!"
    end
  | Error e -> Format.eprintf "KB problem: %a\n%!" KB.Conflict.pp e
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

let build_car : Car.tag KB.obj KB.t =
  let* car = KB.Object.create Car.cls in
  let* () = KB.provide Car.color car "red" in
  KB.return car

let () =
  let state = Bap.Std.Toplevel.current () in
  let result = KB.run Car.cls build_car state in
  match result with
  | Ok (snapshot, _) ->
    begin
      Format.printf "- Snapshot: %a\n%!" KB.Value.pp snapshot;
      let color = KB.Value.get Car.color snapshot in
      Format.printf "- Color: %s\n%!" color
  | Error e -> Format.eprintf "KB Problem: %a\n%!" KB.Conflict.pp e
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

It will print out the snapshot and the color:

```
- Snapshot: ((my.org:color red))
- Color: red
```

Clean up:

```
make clean
```

## Documentation

For more on snapshots (i.e., KB "values"), see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-knowledge/Bap_knowledge/Knowledge/Value/index.html).
