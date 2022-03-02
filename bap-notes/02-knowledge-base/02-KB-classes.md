# Creating KB classes


## KB classes

Every KB class has the following type:

```
('k, 's) KB.cls
```

Note that:
* `'k` is a custom type that serves as a unique tag for the class.
* `'s` is the type of a sorting index that can be used to index sub-classes.


## A mono-sorted example

In a new folder somewhere, create a file called `main.ml`. For convenience, add an alias to the KB module:

```
module KB = Bap_knowledge.Knowledge
```

Then initialize BAP:

```
let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

For a toy example, let's define a class to represent cars.

First, let's encapsulate our definition inside a module:

```
module Car = struct

  (* We'll define the class here *)

end
```

Next, specify a package name (BAP uses this to namespace your classes, so choose a name that uniquely identifies your organizaton):

```
module Car = struct

  let package = "my.org"

end
```

Then specify a type to uniquely tag the class:

```
module Car = struct

  package = "my.org"
  type tag = Car

end
```

Next, we need to specify a type for a sorting index, which can be used to index sub-classes. For this example, let's assume that we don't need further sub-classes. So, we'll just use `unit` as the sort, since it has only one value (namely, `()`):

```
module Car = struct

  package = "my.org"
  type tag = Car
  type sort = unit

end
```

Now declare a class for cars:

```
module Car = struct

  let package = "my.org"
  type tag = Car
  type sort = unit

  let name = "car"
  let desc = "A class representing cars"
  let index = () (* The only value of unit, so the only possible index *)
  let cls : (tag, sort) Kb.cls =
    KB.Class.declare name index ~package ~desc

end
```

We haven't attached any slots to this class yet, but this is a valid class nonethless, and it illustrates the basic procedure behind creating a class: specify a type to use to tag the class and a type to use as a sorting index, and then use `KB.Class.declare name index` to create the class.

At this point, there isn't much we can do with the class, so let's just print its name.

Add a function that uses `KB.Class.name` to extract the name of a class:

```
let get_name (cls : ('k, 's) KB.cls) : string =
  let kb_name = KB.Class.name cls in
  KB.Name.show kb_name
```

Then print the name:

```
let () =
  let name = get_name Car.cls in
  Format.printf "Car class name: %s\n%!" name
```

To summarize, the entire `main.ml` file looks like this:

```
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
