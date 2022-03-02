# Parameters

BAP can collect user-provided parameters from the command line or file, and you can retreive them from within an extension or pass. Parameters are declared using `Bap_main.Extension.Configuration`, and the types of parameters are defined in `Bap_main.Extension.Type`. 

## Declaring a parameter

In a new folder, create a file called `extension_02.ml` with the following:

```
open Core_kernel
open Bap.Std
``` 

For convenience, add the following aliases:

```
module Conf = Bap_main.Extension.Configuration
module Param_type = Bap_main.Extension.Type
```

Declare a parameter called `user`, which is just a string:

```
let user = Conf.parameter Param_type.string "user"
```

Now create an extension that uses `Conf.get` to retrieve the value of that parameter and print it:

```
let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  let user = Conf.get ctxt user in
  printf "Hello, '%s'\n%!" user;
  Ok ()
```

Finally, register the extension:

```
let () =
  Bap_main.Extension.declare run
```

The whole file looks like this:

```
open Core_kernel
open Bap.Std

module Conf = Bap_main.Extension.Configuration
module Param_type = Bap_main.Extension.Type

let user = Conf.parameter Param_type.string "user"

let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  let user = Conf.get ctxt user in
  printf "Hello, '%s'\n%!" user;
  Ok ()

let () =
  Bap_main.Extension.declare run
```

Create a `Makefile`:

```
PUBLIC_NAME := my-extension-02
PUBLIC_DESC := My demo extension 02

NAME := extension_02
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

Run `bap`, e.g.:

```
bap /bin/true
```

It should print out:

```
Hello, ''
```

The user is empty. This is because we did not specify a value for the user parameter. The format for the command line argument is:

```
--<name-of-plugin>-<parameter-name>
```

In this case, the plugin is named `my-extension-02`, and the parameter name is `user`, so the command line argument is:

```
--my-extension-02-user
```

Run `bap` again, but this time, provide a value for that argument:

```
bap /bin/true --my-extension-02-user Alice
```

Now it prints out:

```
Hello, 'Alice'
```

Clean up:

```
make uninstall
make clean
```

## Parameters for passes

Parameters can be retrieved from passes, if the context is sent to the pass. In a new folder, create a file called `pass_02.ml` with the following:

```
open Core_kernel
open Bap.Std

module Conf = Bap_main.Extension.Configuration
module Param_type = Bap_main.Extension.Type
```

Declare two parameters: `user` (a string), and `favorite-num` (an int):

```
let user = Conf.parameter Param_type.string "user"
let fav_num = Conf.parameter Param_type.int "favorite-num"
```

Create a pass that takes a BAP context and a project, and which retrieves the parameters from the context:

```
let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
  let user = Conf.get ctxt user in
  let fav_num = Conf.get ctxt fav_num in
  printf "Hello, '%s', your favorite number is '%d'\n%!" user fav_num
```

Now create an extension that registers the pass, curried with the context:

```
let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' (pass ctxt);
  Ok ()
```

Finally, declare the extension:

```
let () =
  Bap_main.Extension.declare run
```

The whole file looks like this:

```
open Core_kernel
open Bap.Std

module Conf = Bap_main.Extension.Configuration
module Param_type = Bap_main.Extension.Type

let user = Conf.parameter Param_type.string "user"
let fav_num = Conf.parameter Param_type.int "favorite-num"

let pass (ctxt : Bap_main.ctxt) (proj : Project.t) : unit =
  let user = Conf.get ctxt user in
  let fav_num = Conf.get ctxt fav_num in
  printf "Hello, '%s', your favorite number is '%d'\n%!" user fav_num

let run (ctxt : Bap_main.ctxt) : (unit, Bap_main.error) Stdlib.result =
  Project.register_pass' (pass ctxt);
  Ok ()

let () =
  Bap_main.Extension.declare run
```

Create a `Makefile`:

```
PUBLIC_NAME := my-pass-02
PUBLIC_DESC := My demo pass 02

NAME := pass_02
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

Run `bap`, and invoke the pass, e.g.:

```
bap /bin/true --my-pass-02
```

It should print out:

```
Hello, '', your favorite number is '0'
```

Note that `user` defaults to an empty string, and `favorite-num` defaults to `0`. 

Run it again, but provide values for those parameters:

```
bap /bin/true --my-pass-02 --my-pass-02-user Alice --my-pass-02-favorite-num 7 
```

It should print out:

```
Hello, 'Alice', your favorite number is '7'
```

Clean up:

```
make uninstall
make clean
```


## Parameters via environment variables

You can specify parameters as environment variables. The format for the environment variable is:

```
BAP_<name-of-plugin>_<parameter-name>
```

For instance, take the `user` parameter for the `my-pass-02` plugin above. The environment variable for this would be:

```
BAP_MY_PASS_02_USER
```

If this environment variable is set, then BAP will use it when it runs the pass. For instance:

```
BAP_MY_PASS_02_USER=Bob bap /bin/true --my-pass-02
```

It should print out:

```
Hello, 'Bob', your favorite number is '0'
```


## Parameters via configuration files

You can specify the values of parameters in configuration files. The format is:

```
<plugin-name>-<parameter-name>=<value>
```

For instance, if we take the `user` parameter for the `my-pass-02` plugin above, we could specify a value in a configuration file like this:

```
my-pass-02-user=Carol
```

BAP will look for configuration files in `$XDG_CONFIG_HOME/bap`. For instance, on Ubuntu, that would be `${HOME}/.config/bap`. Create that folder:

```
mkdir -p ~/.config/bap
```

Then create a file (it can be named anything) inside that folder, e.g.:

```
touch ~/.config/bap/conf
```

Inside that file, specify a value for the `user` and `favorite-num` parameters:

```
my-pass-02-user=Carol
my-pass-02-favorite-num=13
```

Now run the plugin again:

```
bap /bin/true --my-pass-02
```

It should print out:

```
Hello, 'Carol', your favorite number is '13'
```


## Precedence

BAP evaluates parameters in the following order:

* Config file
* Environment variable
* Command line argument
