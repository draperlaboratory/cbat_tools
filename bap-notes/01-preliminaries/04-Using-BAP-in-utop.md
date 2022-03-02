# Using BAP in utop


## Setup

Open `utop-full` (do not use `utop`):

```
utop-full
```

Then load `bap.top`:

```
#require "bap.top";;
```

It will print a warning about `Core.Time_ns.Ofday.pp`, but you can ignore this. `bap.top` will define a series of custom pretty printers instead, and it will also initialize BAP (it runs `Bap_main.init`).

Tell `utop` to use `topfind`:

```
#use "topfind";;
```

Load `core_kernel` and `bap`:

```
#require "core_kernel";;
#require "bap";;
```

Open `Core_kernel` and `Bap.Std`:

```
open Core_kernel;;
open Bap.Std;;
```

Now you're ready to start exploring BAP in utop.


## Load a binary executable

Define a function that can load a binary executable:

```
let load_exe (filename : string) : project =
  let input = Project.Input.file ~loader:"llvm" ~filename in
  match Project.create input ~package:filename with
  | Ok proj -> proj
  | Error e -> failwith (Error.to_string_hum e)
```

Load an executable, e.g.:

```
let proj = load_exe "/bin/true";;
```

Now you can explore the project. For instance, extract the lifted program:

```
let prog = Project.program proj;;
```

And print it:

```
Format.printf "%a" Program.pp prog;;
```


## Exiting utop

To quit `utop`:

```
#quit
```


