# Using the CLI


## The CLI help

See the main help/usage:

```
bap --help
```

## BAP commands

The `bap` command is a parent command for various subcommands.

List all available subcommands:

```
bap list commands
```

To see the help/usage for any subcommand:

```
bap SUBCOMMAND --help
```

Where `SUBCOMMAND` is replaced by one of the subcommands, e.g.:

```
bap mc --help
```


## Dissassemble and lift

To disassemble and lift a binary executable:

```
bap disassemble /path/to/exe
```

For instance:

```
bap disassemble /bin/true
```

If you run the above command, you will see no output, but BAP did in fact process `/bin/true`, and it stored what it learned in a cache so that the next time you look at `/bin/true` with BAP, it doesn't have to repeat the whole analysis all over again.

To clean the cache:

```
bap cache --clean
```


## The default is `disassemble`

If you do not specify a subcommand, BAP will just use `disassemble`.

So, for instance, you can disassemble a binary executable like this:

```
bap disassemble /path/to/exe
```

Or you can just omit `disassemble` and type this instead:

```
bap /path/to/exe
```

Most examples (in BAP documentation, for example) omit `disassemble` in this manner.


## The lifted IR

To see the lifted IR of a program that BAP has disassembled, add `--dump bir` to the `disassemble` command:

```
bap disassemble /bin/true --dump bir
```

As shortcut, use `-dbir` instead of `--dump bir`:

```
bap disassemble /bin/true -dbir
```

And as an even shorter shortcut, omit `disassemble`:

```
bap /bin/true -dbir
```


## The CFG

To see the CFG that BAP generates for a binary executable:

```
bap /path/to/exe -dcfg
```

Which is shorthand for:

```
bap disassemble /path/to/exe --dump cfg
```

BAP outputs the CFG as a `.dot` file. You can save it into a file if you like:

```
bap /path/to/exe -dcfg > out.dot
```

Then cut and paste the contents of `out.dot` into a dot viewer such as dreampuf.github.io/GraphvizOnline.


## The assembly of a program

To look at the assembly of a program that BAP has lifted:

```
bap /path/to/exe -dasm
```

Which is really just a shorthand for:

```
bap disassemble /path/to/exe --dump asm
```


## Using `bap objdump`

When BAP uses the `disassemble` subcommand to lift a binary program, it builds a control flow graph. If you just want to look at each instruction one after another (a linear sweep), use the `objdump` subcommand:

```
bap objdump /path/to/exe --show-insn=asm
```

To show the ADT instead:

```
bap objdump /path/to/exe --show-insn=adt
```

To show the binary data itself:

```
bap objdump /path/to/exe --show-insn=bin
```

And pipe it through octal dump for display in a terminal:

```
bap objdump /path/to/exe --show-insn=bin | od -h
```


## Using `bap mc`

To see how BAP disassembles a particular stream of bytes, use the `bap mp` command. For instance:

```
bap mc --show-insn=asm -- 48 83 ec 08
```
