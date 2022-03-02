# Custom command errors

A custom command returns `Ok ()` or a `Bap_main.error`. `Bap_main.error` is an extensible type, so you can add your own variants, and write your own error printer to handle your variants.


## Example

In a new folder, create a file `command_01.ml`, with the following:

```
open Core_kernel

module Param_type = Bap_main.Extension.Type
module Cmd = Bap_main.Extension.Command
module Err = Bap_main.Extension.Error
```

Next, add a custom error constructor `Fail`:

```
type Err.t += Fail of string
```

Add a custom printer that returns `Some <string>` for `Fail <string>`:

```
let error_printer (e : Err.t) : string option =
  match e with
  | Fail s -> Some (sprintf "My custom command error: %s" s)
  | _ -> None
```

Next, add in your command CLI, e.g.:

```
module Cli = struct

  let name = "my-command-01"
  let doc = "Another demo BAP command"

  let job_title = Cmd.parameter Param_type.string "job-title"
    ~doc:"Your job title"

  let first_name = Cmd.argument Param_type.string
    ~doc:"Your first name"

  let grammar = Cmd.(args $ job_title $ first_name)

  let callback (job_title : string) (first_name : string)
    (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) result =
    match first_name with
    | "Jo" ->
      Error (Fail "Jo, you can't be here")
    | _ ->
      printf "First name: %s\n%!" first_name;
      printf "Job title: %s\n%!" job_title;
      Ok ()

end
```

Notice that if the first name is `Jo`, the callback returns a `Fail` error, otherwise it returns `Ok ()`.

Finally, register the custom error printer, and declare the command:

```
let () =
  Err.register_printer error_printer;
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc
```

The whole file looks like this:

```
open Core_kernel

module Param_type = Bap_main.Extension.Type
module Cmd = Bap_main.Extension.Command
module Err = Bap_main.Extension.Error

type Err.t += Fail of string

let error_printer (e : Err.t) : string option =
  match e with
  | Fail s -> Some (sprintf "My custom command error: %s" s)
  | _ -> None

module Cli = struct

  let name = "my-command-01"
  let doc = "Another demo BAP command"

  let job_title = Cmd.parameter Param_type.string "job-title"
    ~doc:"Your job title"

  let first_name = Cmd.argument Param_type.string
    ~doc:"Your first name"

  let grammar = Cmd.(args $ job_title $ first_name)

  let callback (job_title : string) (first_name : string)
    (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) result =
    match first_name with
    | "Jo" ->
      Error (Fail "Jo, you can't be here")
    | _ ->
      printf "First name: %s\n%!" first_name;
      printf "Job title: %s\n%!" job_title;
      Ok ()

end

let () =
  Err.register_printer error_printer;
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc
```

Add a `Makefile`:

```
PUBLIC_NAME := my-command-01
PUBLIC_DESC := My demo command 01

NAME := command_01
SRC := $(NAME).ml
PLUGIN := $(NAME).plugin


#####################################################
# DEFAULT
#####################################################

.DEFAULT_GOAL := all

all: clean uninstall install


#####################################################
# THE PLUGIN
#####################################################

.PHONY: clean
clean:
        bapbuild -clean

uninstall:
        bapbundle remove $(PLUGIN)

build: $(SRC)
        bapbuild -use-ocamlfind -package findlib.dynload $(PLUGIN)

install: build
        bapbundle update -name $(PUBLIC_NAME) $(PLUGIN)
        bapbundle update -desc "$(PUBLIC_DESC)" $(PLUGIN)
        bapbundle install $(PLUGIN)
```

Build and install:

```
make
```

Confirm that your command got installed:

```
bap list commands
```

You should see it listed:

```
  my-command-01            another demo BAP command
```

Run the command:

```
bap my-command-01 "Tom" --job-title "Sales associate"
```

It should print out:

```
First name: Tom
Job title: Sales associate
```

Now run the command, but with the name "Jo":

```
bap my-command-01 "Jo" --job-title "Engineer"
```

That triggers the error:

```
My custom command error: Jo, you can't be here
```

Clean up:

```
make uninstall clean
```

