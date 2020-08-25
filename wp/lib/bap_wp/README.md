# Weakest Precondition library

A weakest-precondition analysis library, called `bap_wp`. This library is used by the `wp` plugin (see the parent directory [README](./../../README.md)).


## Build/Install

Before installing, make sure you have the required dependencies installed on your system. See the build/install/test instructions in the [website](https://draperlaboratory.github.io/cbat_tools/installation.html#manual) for details.

Once the dependencies are installed, build by running the following `make` command from this directory:

    make build

To install the package locally:

    make install.local

Confirm that `bap_wp` is installed:

    ocamlfind query bap_wp
    opam show bap_wp

Confirm the library can be used in `utop`:

    #use "topfind";;
    #require "bap_wp";;

Then make sure you can auto-complete, e.g.:

    Bap_wp.Precondition...
    #quit;;


### Quality

Run all tests:

    make test

Run only unit tests:

    make test.unit

Run only performance tests:

    make test.performance


### Documentation

If you have `odoc` installed, you can build the documentation with:

    make doc

The documentation can then be found here:

    _build/default/_doc


### Uninstall/clean (local)

To uninstall and clean locally:

    make clean.local

Confirm that `bap_wp` can no longer be found:

    ocamlfind query bap_wp
    opam show bap_wp


## A Note on Usage

The easiest way to use this library is directly through the BAP plugin (see the parent [README.md](./../../README.md)), which provides a command line interface for it. However, it may also be used as a standalone OCaml library, to invoke a WP computation over a bap subroutine or block.

The file `src/precondition.mli` describes the main API. The general approach is to use `mk_env` to create an analysis environment, and then call `visit_sub` with a given postcondition and subroutine, to get the corresponding precondition, which can then be checked with `check`.
