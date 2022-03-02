# Multisorted KB classes

## KB classes

Recall that every KB class has the following type:

```
('k, 's) KB.cls
```

Note that:
* `'k` is a custom type that serves as a unique tag for the class.
* `'s` is the type of a sorting index that can be used to index sub-classes.

The `'s` parameter can be used to distinguish different sub-classes.


## Many-sorted example

In a new folder somewhere, create a file called `main.ml`. Add a `KB` alias and initialize BAP:

```
module KB = Bap_knowledge.Knowledge

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

For a many-sorted example, let's define a class to represent employees.

Fist, create a module to encapsulate the definition, and specify a package name and a tag for the class:

```
module Employee = struct

  package = "my.org"
  type tag = Employee

end
```

Now for a sorting index. Let's index our sub-classes by whether the employee is a member of the sales team, marketing team, or executive team:

```
module Employee = struct

  package = "my.org"
  type tag = Employee
  type sort = Sales | Marketing | Executive

end
```

Declare a class for employees on the sales team:

```
module Employee = struct

  package = "my.org"
  type tag = Employee
  type sort = Sales | Marketing | Executive

  let name = "sales-employee"
  let desc = "A class representing employees on the sales team"
  let index = Sales
  let sales_empl : (tag, sort) KB.cls =
    KB.Class.declare name index ~package ~desc

end
```

Declare another class, this time for employees on the executive team:

```
module Employee = struct

  package = "my.org"
  type tag = Employee
  type sort = Sales | Marketing | Executive

  let name = "sales-employee"
  let desc = "A class representing employees on the sales team"
  let index = Sales
  let sales_cls : (tag, sort) KB.cls =
    KB.Class.declare name index ~package ~desc

  let name = "executive-employee"
  let desc = "A class representing employees on the executive team"
  let index = Executive
  let executive_cls : (tag, sort) KB.cls =
    KB.Class.declare name index ~package ~desc

end
```

We haven't attached any slots to these classes, so let's just display the names of these classes:

```
let get_name (cls : ('k, 's) KB.cls) : string =
  let kb_name = KB.Class.name cls in
  KB.Name.show kb_name

let () =
  let sales_class_name = get_name Employee.sales_cls in
  let executive_class_name = get_name Employee.executive_cls in
  Format.printf "Sales class name: %s\n%!" sales_class_name;
  Format.printf "Executive class name: %s\n%!" executive_class_name
```

To summarize, the entire `main.ml` file looks like this:

```
module KB = Bap_knowledge.Knowledge

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"

module Employee = struct

  package = "my.org"
  type tag = Employee
  type sort = Sales | Marketing | Executive

  let name = "sales-employee"
  let desc = "A class representing employees on the sales team"
  let index = Sales
  let sales_cls : (tag, sort) KB.cls =
    KB.Class.declare name index ~package ~desc

  let name = "executive-employee"
  let desc = "A class representing employees on the executive team"
  let index = Executive
  let executive_cls : (tag, sort) KB.cls =
    KB.Class.declare name index ~package ~desc

end

let get_name (cls : ('k, 's) KB.cls) : string =
  let kb_name = KB.Class.name cls in
  KB.Name.show kb_name

let () =
  let sales_class_name = get_name Employee.sales_cls in
  let executive_class_name = get_name Employee.executive_cls in
  Format.printf "Sales class name: %s\n%!" sales_class_name;
  Format.printf "Executive class name: %s\n%!" executive_class_name
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

Now run the program:

```
make
```

It will print out the names of the classes:

```
Sales class name: my.org:sales-employee
Executive class name: my.org:executive-employee
```

Clean up:

```
make clean
```
