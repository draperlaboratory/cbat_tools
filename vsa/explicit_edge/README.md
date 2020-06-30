This plugin is intended to utilize the results of value-set analysis to
complete a program's CFG by replacing indirect jumps with direct ones where
possible. It does this by replacing each indirect jump with a sequence of
conditional direct jumps when the possible targets can be reduced to a
sufficiently small number.

Build
--------------
### Prerequisites

Before installing `explicit_edge`, the following requirements must be met:

* BAP 2.0.0-alpha+ must be available. Confirm with `bap --version`.
* core 0.12.4+ must be available. Confirm with `ocamlfind query core`.
* ppx\_deriving must be available. Confirm with `ocamlfind query ppx_deriving`
* cbat\_value\_set must be available. Confirm with `ocamlfind query cbat_value_set`
* Dune 1.6+ must be available. Confirm with `dune --version`.

### Installation

To build and install the plugin:

    make

To uninstall and clean:

    make clean

To remove any current installation of the plugin and reinstall:

    make reinstall

Flags
--------------
Note that all value-set flags will still work (see [value-set README](../value_set/README.md))
since running this pass will first run a value-set pass.

- `sub`: The name of the subroutine to transform. If not provided, the transform
  will run on all subroutines. Note that this differs from the `--value-set-sub`
  flag since the VSA will still be run on the whole program and the whole program
  will be returned, rather than a single subroutine.


Running a pass
----------------
To run the pass on a binary, run `bap [FILE] -p explicit-edge [OPTIONS]` where
`[FILE]` is the binary to analyze and `[OPTIONS]` is a sequence of the form
`--explicit-edge-[OPTION] [VALUE] ...` where `[OPTION]` is from the list above and
`[VALUE]` is the value of the argument. See `bap --help` and `bap --explicit-edge-help`
for more details.
