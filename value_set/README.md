This plugin is intended to implement value set analysis for the purpose of
recovering the full control flow graph from a program with indirect jumps.  It
uses circular linear progressions to abstract over sets of possible values.

Build
--------------

This plugin is built using OASIS. Make sure to have OPAM and OASIS installed
before building (OASIS can be installed via `opam install oasis`).  This
plugin also requires version 1.5.0 of BAP (currently the GitHub [master
branch](https://github.com/BinaryAnalysisPlatform/bap)).  For difficulties
installing BAP, see the BAP build instructions. The package `ppx_deriving` is
also required for this plugin. To install, run `opam install ppx_deriving`
Once BAP and `ppx_deriving` are installed, running `make` from the `value_set`
directory should build the plugin. Running `make reinstall` should replace the
current install (if any) and register the plugin with BAP.

Flags
--------------

- `sub`: This flag takes one argument, the name of the subroutine to
  analyze. If this argument is provided, VSA is run only on the named routine.

- `keep-trying`: When this flag is present, uses broad approximations for
  unimplemented code.  This is occasionally unsound.  For example, with this
  flag "top" will be used when a division by zero is detected, which may not
  accurately model the program crashing.

- `unsound-stack`: When this flag is present, uses an unsound initial value of
  0 for RSP.  This greatly improves accuracy of memory usage.

- `show-vsa`: "Whether to print the output of the VSA pass on the command
  line.  If true, will print the result of the VSA. Set to false to stop this
  feature from interfering with passing program dumps via stdout.


Running a pass
----------------

If the plugin is not loaded, run `make -s plugin`.

To execute an analysis, run `bap [FILE] -p value-set [OPTIONS]` where `[FILE]`
is the binary to analyze and `[OPTIONS]` is a sequence of the form
`--value-set-[OPTION] [VALUE] ...` where `[OPTION]` is from the list above and
`[VALUE]` is the value of the argument. See `bap --help` and `bap
--value-set-help` for more details.
