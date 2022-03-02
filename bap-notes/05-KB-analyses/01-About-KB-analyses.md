# About KB Analyses

In BAP terminology, a "pass" is an analysis that explores a disassembled project/program. A "KB analysis" is a similar idea, but a KB analysis explores the knowledge base. 

You can register your KB analyses with BAP, and specify a command line interface to them. BAP has a REPL that lets you run your command from the REPL, but you can also trigger the command in batch mode, or even from a script.


## The REPL

To start a bare REPL (i.e., with no knowledge base loaded up), type the following and hit `<enter>`:

```
bap analyze
```

You will see a REPL prompt:

```
bap> 
```

To list the registered commands, type `commands` and hit `<enter>`:

```
bap> commands
```

BAP will then print the list of available commands, e.g.:

```
bap:subroutines                          prints all subroutines
bap:units                                prints all units
bap:subroutine                           prints a subroutine
bap:instructions                         prints all instructions
bap:instruction                          prints the instruction semantics
```

The commands are listed on the left, and a description of each one is on the right.

To see the help for any command, type `help <command>`. For instance:

```
bap> help bap:units
bap> help bap:subroutines
```

Try to run a command. For instance, type `bap:units` and hit `<enter>`:

```
bap> bap:units
```

It prints nothing, and returns the REPL prompt:

```
bap>
```

This is because we started the REPL without any knowledge base loaded up.

To exit the REPL, type `quit` and hit `<enter>`:

```
bap> quit
```


## Loading a knowledge base

The REPL can load up a knowledge base from a file. First, dump a project to a file. For instance, to dump `/bin/true` to a file called `test.proj`:

```
bap /path/to/bin --project test.proj --update
```

Next, start the analysis REPL with that project:

```
bap analyze --project test.proj
```

That starts the REPL, with the knowledge base for the project loaded into memory.

Now that we have a knowledge base loaded up, run the `bap:units` command:

```
bap> bap:units
```

It lists the sole compilation unit of the program:

```
file:/bin/true                           bap:amd64
```

The name of the code unit is on the left, and the name of the target architecture is on the right.

Now use the `bap:subroutines` command to list the subroutines associated with this code unit:

```
bap> bap:subroutines file:/bin/true
```

The output is a big list of all of the subroutines in the project:

```
/bin/true:__ctype_b_loc\:external: __ctype_b_loc:external
/bin/true:iswprint\:external: iswprint:external
/bin/true:mbsinit\:external: mbsinit:external
/bin/true:__fprintf_chk\:external: __fprintf_chk:external
/bin/true:fwrite\:external: fwrite:external
/bin/true:exit\:external: exit:external
...
```

Exit the REPL:

```
bap> quit
```


## Documentation

To see the source code for the built-in analysis commands, see [here](https://github.com/BinaryAnalysisPlatform/bap/tree/master/plugins/analyze). For more about KB analyses in general, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Project/Analysis/index.html).
