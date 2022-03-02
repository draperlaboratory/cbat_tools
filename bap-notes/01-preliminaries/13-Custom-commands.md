# Custom commands

The BAP CLI knows about a number of subcommands. To see them all:

```
bap list commands
```

Each of the commands that it lists has its own further command line parameters, positional arguments, and options. E.g.:

```
bap mc --help
```

You can create your own custom command, and add it to BAP.


## Example

In a new folder, create a file called `command_00.ml` with the following:

```
open Core_kernel
```

Add the following module aliases for convenience:

```
module Param_type = Bap_main.Extension.Type
module Cmd = Bap_main.Extension.Command
```

Next, create a `Cli` module, and specify a name and a doc string for the command:

```
module Cli = struct

  let name = "my-command-00"
  let doc = "A demo BAP command"

end
```

Next, create a `--job-title` parameter that takes a string:

```
  let job_title = Cmd.parameter Param_type.string "job-title"
    ~doc:"Your job title"
```

Create a positional argument:

```
  let first_name = Cmd.argument Param_type.string
    ~doc:"Your first name"
```

Now, specify the grammar of the command's arguments by listing them in order, separated by the `$` operator:

```
  let grammar = Cmd.(args $ job_title $ first_name)
```

Finally, create a callback that BAP can invoke when a user calls your command. The callback should take as arguments the CLI parameters, and a `Bap_main.ctxt`. It should return `Ok ()`, or a `Bap_main.error`. Here is an example:

```
  let callback (job_title : string) (first_name : string)
    (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) result =
    printf "First name: %s\n%!" first_name;
    printf "Job title: %s\n%!" job_title;
    Ok ()
```

Now, declare the command:

```
let () =
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc
```

This tells BAP the name of the command, the grammar for the arguments, the callback it should invoke when a user calls the command, and the doc string. 

The whole file looks like this:

```
open Core_kernel

module Param_type = Bap_main.Extension.Type
module Cmd = Bap_main.Extension.Command

module Cli = struct

  let name = "my-command-00"
  let doc = "A demo BAP command"

  let job_title = Cmd.parameter Param_type.string "job-title"
    ~doc:"Your job title"

  let first_name = Cmd.argument Param_type.string
    ~doc:"Your first name"

  let grammar = Cmd.(args $ job_title $ first_name)

  let callback (job_title : string) (first_name : string)
    (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) result =
    printf "First name: %s\n%!" first_name;
    printf "Job title: %s\n%!" job_title;
    Ok ()

end

let () =
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc
```

Add a `Makefile`:

```
PUBLIC_NAME := my-command-00
PUBLIC_DESC := My demo command 00

NAME := command_00
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

Confirm that your command is installed:

```
bap list commands
```

You should see in the list:

```
  my-command-00            a demo BAP command
```

See the help:

```
bap my-command-00 --help
```

It will list the full help (which includes the parameters/arguments you specified, but also many other parameters that your command inherits from BAP).

Run the command:

```
bap my-command-00 "Jo" --job-title="Engineer"
```

It should print:

```
First name: Jo
Job title: Engineer
```

Clean up:

```
make uninstall clean
```
