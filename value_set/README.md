This plugin is intended to implement value set analysis for the purpose
of recovering the full control flow graph from a program with indirect jumps.
It uses circular linear progressions to abstract over sets of possible values.

Build
--------------

### Prerequisites

Before installing `value_set`, the following requirements must be met:

* BAP 1.6+ must be available. Confirm with `bap --version`.
* core 0.11+ must be available. Confirm with `ocamlfind query core`.
* ppx\_deriving must be available. Confirm with `ocamlfind query ppx_deriving`
* oUnit must be available to `findlib` under the name `oUnit`
  (confirm with `ocamlfind query oUnit`) and it must be available
  to `opam` under the name `ounit` (confirm with `opam show ounit`).
* Dune 1.6+ must be available. Confirm with `dune --version`.
* To build the documentation, you need odoc 1.4.0, which can also be
  installed with `opam install odoc`.

### Installation

To build and install the plugin:

    make

To uninstall and clean:

    make clean

To remove any current installation of the plugin and reinstall:

    make reinstall

### Testing

To run unit tests:

    make test

### Documentation

To build documentation on the library:

    make doc

Flags
--------------

- `sub`: The name of the subroutine to analyze.
         If this argument is provided, VSA is run only on the named routine.
- `keep-trying`: When this flag is present, uses broad approximations for unimplemented code
- `unsound-stack`: When this flag is present, uses an unsound initial value of 0 for RSP.
                   This greatly improves accuracy of memory usage.
- `show-vsa`: "Whether to print the output of the VSA pass on the command line.
              If true, will print the result of the VSA. Set to false to stop
              this feature from interfering with passing program dumps via stdout.


Running a pass
----------------
If the plugin is not loaded, run `make -s plugin`.
To execute an analysis, run `bap [FILE] -p value-set [OPTIONS]` where
`[FILE]` is the binary to analyze and `[OPTIONS]` is a sequence of the form
`--value-set-[OPTION] [VALUE] ...` where `[OPTION]` is from the list above and
`[VALUE]` is the value of the argument. See `bap --help` and `bap --value-set-help`
for more details.
