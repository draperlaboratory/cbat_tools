# KB domains

Every KB slot has a domain, which is a specified range of values that it can hold.

Domains are special, because the values in a domain are ordered by their informativeness.

There is always a bottom element, which represents "we have no information about this." Then, all of the other values stand above that (as a flat array, or as an ascending chain, or as a lattice, and so on).

BAP allows us to add a value to a slot only if the value we are putting in is more informative than what was in the slot before.


## Example

In a new folder somewhere, create a file called `main.ml` with the following:

```
open Core_kernel

module KB = Bap_knowledge.Knowledge

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"
```

Define a flat domain that can hold strings, where the empty element is the empty string:

```
let string_domain : string KB.Domain.t =
  KB.Domain.flat "string-domain"
    ~inspect:(fun s -> Sexp.Atom s)
    ~equal:String.(=)
    ~empty:""
```

Note that we provided an `inspect` function, which converts the value into an S-expression. This lets BAP print values in the domain nicely.

We aren't doing anything with this domain yet, so for now let's just display its name:

```
let () =
  let name = KB.Domain.name string_domain in
  Format.printf "Domain name: %s\n%!" name
```

Create a domain that takes optional boolean values:

```
let optional_bool_domain : bool option KB.Domain.t =
  KB.Domain.optional "optional-bool-domain"
    ~inspect:(fun b -> Sexp.Atom (Bool.to_string b))
    ~equal:Bool.(=)
```

Print the domain's name:

```
let () =
  let name = KB.Domain.name optional_bool_domain in
  Format.printf "Domain name: %s\n%!" name
```

To summarize, here is the entire `main.ml` file:

```
open Core_kernel

module KB = Bap_knowledge.Knowledge

let () = match Bap_main.init () with
  | Ok () -> ()
  | Error _ -> failwith "Error initializing BAP"

let string_domain : string KB.Domain.t =
  KB.Domain.flat "string-domain"
    ~inspect:(fun s -> Sexp.Atom s)
    ~equal:String.(=)
    ~empty:""

let () =
  let name = KB.Domain.name string_domain in
  Format.printf "Domain name: %s\n%!" name

let optional_bool_domain : bool option KB.Domain.t =
  KB.Domain.optional "optional-bool-domain"
    ~inspect:(fun b -> Sexp.Atom (Bool.to_string b))
    ~equal:Bool.(=)

let () =
  let name = KB.Domain.name optional_bool_domain in
  Format.printf "Domain name: %s\n%!" name
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

.PHONEY: clean
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

It will print out the names of the two domains:

```
Domain name: string-domain
Domain name: optional-bool-domain
```

Clean up:

```
make clean
```

## Documentation

For more details about the different kinds of domains, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-knowledge/Bap_knowledge/Knowledge/Domain/index.html).
