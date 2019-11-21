# Weakest Precondition library

A weakest-precondition analysis library, for BAP plugins/tools.


## Installation

### Prerequisites

Before installing `bap_wp`, the following requirements must be met:

* BAP 2.0.0+ must be available. Confirm with `bap --version`.
* z3 4.8.6+ must be available to `findlib` under the name `z3`
  (note the lowercase `z`). Confirm with `ocamlfind query z3`.
* core 0.11+ must be available. Confirm with `ocamlfind query core`.
* oUnit must be available to `findlib` under the name `oUnit`
  (confirm with `ocamlfind query oUnit`) and it must be available
  to `opam` under the name `ounit` (confirm with `opam show ounit`).
* Dune 1.6+ must be available. Confirm with `dune --version`.
* To build the documentation, you need odoc 1.4.0, which can also be
  installed with `opam install odoc`.


### Install (local)

To build:

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

Build with

    make doc

Which can then be found in

    _build/default/_doc

### Uninstall/clean (local)

To uninstall and clean locally:

    make clean.local

Confirm that `bap_wp` can no longer be found:

    ocamlfind query bap_wp
    opam show bap_wp


## Overview

The easiest way to use this library is directly through the BAP
plugin. However, it may also be used as a standalone library, to
invoke a WP computation over a bap subroutine or block.

The file [src/precondition.mli] describes the main API. The general
approach is to use `mk_default_env` or `mk_inline_env` to create an
analysis environment, and then call `visit_sub` with a given
postcondition and subroutine, to get the corresponding precondition,
which can then be checked with `check`.
