# WP

## Build/install/test

Depends on:

    - ocaml 4.05.0
    - core_kernel 0.11
    - bap 1.6
    - ounit 2.0.8
    - z3 4.8.4

All these can be installed with

    opam install package_name

To build and install the plugin:

    make

To uninstall and clean:

    make clean

To run oUnit tests:

    make test

## Example

Take the following C code:

```
#include <assert.h>

int main(int argc,char ** argv) {


  if(argc == 3)
    assert(0);


  return 0;
}

```

Compile with

> gcc -g -o my_exec my_code.c

And then invoke the bap plugin with

> bap my_exec --pass=wp

You should get an output which includes something like the following:

```
SAT!
Model:
(define-fun RDI0 () (_ BitVec 64)
  #x0000000000000003)
```

Given that the `argc` argument is kept in the `RDI` register on
`X86_64` architectures, this give us possible input register values to
reach the `assert(0)` statement on line 7 of the source.

Changing line 6 to
```
if(argc != 3)
```

results in

```
UNSAT!
```

Meaning there is no way to reach the `assert(0)` statement.

-------

A more sophisticated example involves comparing two different
programs, in order to prove or refute functional equivalence of
subroutines.

We create 2 similar C programs:

`main_1.c`:
```
#include <stdbool.h>
#include <stdio.h>

typedef enum {SURFACE, TEST, RECORD, NAV, DEPLOY, LOG_STATUS} status_t;

bool process_status(status_t status) {
  bool nav = false;
  bool log = false;
  bool deploy = false;

  switch (status) {
    case NAV:
      nav = true;

    case LOG_STATUS:
      log = true;
      break;

    case DEPLOY:
      deploy = true;
      break;
  }
  return deploy;
}

int main() {

  status_t status = NAV;

  if (process_status(status)) {
    printf("Payload deployed.\n");
  }

  return 0;
}

```

and `main_2.c`:
```
#include <stdbool.h>
#include <stdio.h>

typedef enum {SURFACE, TEST, RECORD, NAV, DEPLOY} status_t;

bool process_status(status_t status) {
  bool nav = false;
  bool deploy = false;

  switch (status) {
    case NAV:
      nav = true;

    case DEPLOY:
      deploy = true;
      break;
  }
  return deploy;
}

int main() {

  status_t status = NAV;

  if (process_status(status)) {
    printf("Payload deployed.\n");
  }

  return 0;
}

```

So, `main_2.c` simply removes the `LOG_STATUS` case in the
`process_status` function, and in the enum.

As one might already notice, there is no break statement after the
`NAV` case, in which case the fall-through will create different
semantics for the return value.

To invoke `wp` on pairs of binaries, it is necessary to compile
each C file, and then call the `save-project` pass which creates a
serialized form of the decompiled code. To do this, invoke:

> gcc -g -o main_1 main_1.c

and

> gcc -g -o main_2 main_2.c

and then

> bap --pass=save-project main_1 && bap --pass=save-project main_2

which should create the `main_1.bpj` and `main_2.bpj` serialized files.

One can then invoke the `wp` plugin to compare the functional
behavior of that function, using the invocation:

> bap dummy_binary --pass=wp --wp-compare=true --wp-file1=main_1.bpj --wp-file2=main_2.bpj --wp-function=process_status

Where `dummy_binary` is any valid binary file, it will be
ignored. Note that we pass in the function name we are interested in,
here `process_status`.

This gives a result including many assignments to registers and
variables in the decompiled code, which should include something along
the lines of:

```
(define-fun RBP0 () (_ BitVec 64)
  #x0000000000000000)
(define-fun ZF0 () (_ BitVec 1)
  #b0)
(define-fun RDI30 () (_ BitVec 64)
  #x0000000000000003)
```
As in the single program example, this gives values for registers
which exercise unwanted behavior. In this case, invoking
`process_status` with these register values will give different
outputs depending on whether `main_1` or `main_2` is invoked, which is
unsurprising given that `RDI` is the input value, and `3` is the
numerical value corresponding to the `NAV` case.

One can fix this difference, by adding a break statement after the
`NAV` case in `main_2.c`:

```
case NAV:
  nav = true;
  break;
```

And a similar invocation of bap will indeed give `UNSAT`, meaning that
the return values are always identical for identical inputs.


## Invocation

Use the bap CLI:

To find the precondition of a subroutine:

    bap /path/to/exec --pass=wp \
      [--wp-function=function_name] \
      [--log-dir=directory]

To compare two binaries:

    bap /path/to/dummy/exec --pass=wp \
      --wp-compare=true \
      --wp-file1=/path/to/main1.bpj \
      --wp-file2=/path/to/main2.bpj \
      [--wp-function=function_name] \
      [--wp-check-calls=bool] \
      [--log-dir=directory]

The various options are:

- `--wp-compare=[true|false]`. This flag determines whether or
  not to analyze a single function. If enabled, you will need to
  specify the `file1` and `file2` options as well. `false` by default.
- `--wp-function=function_name`. Determines which function to
  verify. `wp` verifies a single function, though calling it on
  the `main` function along with the `inline` option will analyze the
  whole program. Has value `main` by default.
- `--wp-file1=file_name.bpj`. Determines the location of the
  first file in the case of a comparative analysis.
- `--wp-file2=file_name.bpj`. Determines the location of the
  second file in the case of a comparative analysis.
- `--wp-inline=[true|false]`. Determines whether to inline a
  function call for the purpose of computing the semantics. By default
  we simply build a summary, which is a heuristic representation of
  the function call semantics. `false` by default.
- `--wp-check-calls=[true|false]`. Determines whether to compare
  the semantics of two programs by examining the return values of the
  function to be compared, or whether to compare which sub-routines
  are invoked in the body of the function. `false` by default.
- `--wp-postcond=smt-lib-string`. If present, replaces the
  default post-condition by the user-specified one, using the
  [smt-lib2] format. At the moment, the names of variables
  representing memory and registers are a bit magical, so consider
  this to be an experimental feature.

## C checking API

There is a `cbat.h` file in the `api/c` folder which contains headers
for functions which `wp` handles specially. These are taken to
be identical as in the SV\_COMP competition, and contain a reference
implementation representing their semantics (which is not actually used by the
tool, though).

These can be used to verify certain properties, e.g. a call
```
if (p == NULL) { __VERIFIER_error(); }
```
will check whether `p` may take a `NULL` value. Similarly,

```
char c = __VERIFIER_nondet_char();
```
will assume an unknown value for variable `c`.


## Logging

By default, logs are printed to `STDERR`. You can save the logs to a file by specifying a log directory with the `--log-dir` flag or exporting the `$BAP_LOG_DIR` environment variable.

By default, `debug` logs are not shown. To show debug logs:

    export BAP_DEBUG=true

