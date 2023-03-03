# Plugins

BAP can be extended in various ways with your own custom code.

A package that you create that extends BAP is called a *plugin*. 

To see a list of available plugins for your local BAP installation:

```
bap list plugins
```

Plugins are built (compiled) with the `bapbuild` tool that ships with BAP:

```
bapbuild -help
```

Plugins are installed with the `bapbundle` tool that ships with BAP:

```
bapbundle -help
```

Note: to avoid undefined behavior, always tell `bapbuild` to use `ocamlfind` and the `findlib.dynload` library, e.g.:

```
bapbuild -use-ocamlfind -package findlib.dynload ...
```


## A hello world example

Create a file (in some folder) called `plugin00.ml` with these contents:

```
let () = print_endline "Hello, world!"
```

Create a `Makefile`:

```
NAME := plugin00
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
        bapbundle install $(PLUGIN)

```

To build and install it:

```
make
```

To accomplish this, the `Makefile` first builds the plugin:

```
bapbuild -use-ocamlfind -package findlib.dynload plugin00.plugin
```

Then it installs it:

```
bapbundle install plugin00.plugin
```

At this point, the plugin has been installed in your local BAP plugin ecosystem.

Note that plugin code is just this:

```
let () = print_endline "Hello, world!"
```

This code simply tells the system to print "Hello, world!" whenever this module is executed.

But when is it executed? 

This module has been installed as a plugin, so it will be exeuted every time the `bap` command line tool is invoked. 

To confirm that, try any BAP command, e.g.:

```
bap disassemble /bin/true
```

Notice that BAP prints "Hello, world!" This demonstrates that BAP has indeed loaded the plugin when it starts up.

Obviously, this plugin is useless. A more useful plugin will hook into one of BAP's extension points. But more on that later. This example is just for illustration.

To check that a plugin is installed, list all plugins:

```
bap list plugins
```

In this case, you should see that `plugin00` is on the list.

To uninstall and clean:

```
make uninstall clean
```

To carry this out, the `Makefile` first uninstalls the plugin:

```
bapbundle remove plugin00.plugin
``` 

Then it cleans the workspace:

```
bapbuild -clean
```

To confirm that a plugin is no longer installed, list all plugins:

```
bap list plugins
```

You should then see that `plugin00` is no longer on the list.


## Underscores in plugin names

You can use underscores in the filenames. Rename `plugin00.ml` to `plugin_00.ml`, and in the `Makefile`, change `NAME := plugin00` to `NAME := plugin_00`. Then build and install again:

```
make
```

Look at the plugin that BAP has installed now:

```
bap list plugins
```

Notice that BAP lists it as `plugin-00`. When you build and install a plugin from a file `NAME.ml`, BAP will name the plugin `NAME`, but it will replace underscores with hyphens.

Clean and uninstall:

```
make uninstall clean
```

## Custom plugin names and descriptions

A custom name and description can be added to a plugin, using `bapbundle update`. Change the `install` target in the `Makefile` to this:

```
install: build
        bapbundle update -name "my-plugin-00" $(PLUGIN)
        bapbundle update -desc "My hello-world plugin" $(PLUGIN)
        bapbundle install $(PLUGIN)
```

Build and install it:

```
make
```

Look at the name of the plugin:

```
bap list plugins
```

It is listed as `my-plugin-00`, and it has a description `My hello-world plugin`.

To remove a plugin with a custom name, you must refer to it by `FILENAME.plugin`, not `CUSTOM_NAME.plugin`. For instance, try this:

```
bapbundle remove my-plugin-00.plugin
```

Notice that `bapbundle` executes this without error, and it returns a zero exit code, as if to indicate "success":

```
echo $?
```

However, the plugin has not been removed. Confirm this by listing the plugins:

```
bap list plugins
```

To truly uninstall the plugin, you must uninstall `FILENAME.plugin`:

```
bapbundle remove plugin_00.plugin
```

Now you can see that the plugin has been removed:

```
bap list plugins
```

The `Makefile` calls the correct `bapbundle remove` command.
