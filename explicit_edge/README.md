This plugin is intended to utilize the results of value-set analysis to
complete a program's CFG by replacing indirect jumps with direct ones where
possible. It does this by replacing each indirect jump with a sequence of
conditional direct jumps when the possible targets can be reduced to a
sufficiently small number.

Build
--------------
This plugin is built using OASIS. Make sure to have OPAM and OASIS installed
before building. This plugin also requires version 1.5.0 of BAP (currently
the GitHub [master branch](https://github.com/BinaryAnalysisPlatform/bap)).
For difficulties installing BAP, see the BAP build instructions. Once BAP
is installed, running `make` should build the plugin. Running `make reinstall`
should replace the current install (if any) and register the plugin with BAP.

Flags
--------------
Note that all value-set flags will still work (see [value-set README](../value_set/README.md))
since running this pass will first run a value-set pass.

- `sub`: The name of the subroutine to transform. If not provided, the transform
  will run on all subroutines. Note that this differs from the `--value-set-sub`
  flag since the VSA will still be run o nthe whole program and the whole program
  will be returned, rather than a single subroutine.


Running a pass
----------------
To run the pass on a binary, run `bap [FILE] -p explicit-edge [OPTIONS]` where
`[FILE]` is the binary to analyze and `[OPTIONS]` is a sequence of the form
`--explicit-edge-[OPTION] [VALUE] ...` where `[OPTION]` is from the list above and
`[VALUE]` is the value of the argument. See `bap --help` and `bap --explicit-edge-help`
for more details.
