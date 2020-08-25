# Weakest Precondition Analysis (WP)

The weakest precondition analysis consists of two parts.

* A weakest precondition [OCaml library](./lib/bap_wp), which can be installed and used on its own for general weakest precondition analysis.

* A weakest precondition [BAP plugin](./plugin), which provides a convenient command line interface to the just mentioned weakest precondition library.

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

> bap wp --func=main my_exec

You should get an output which includes something like the following:

```
SAT!
Model:
    RDI  |->  #x000000000000003
```

Given that the `argc` argument is kept in the `RDI` register on
`X86_64` architectures, this give us possible input register values to
reach the `assert(0)` statement on line 7 of the source.

Changing line 6 to
```
if((argc == 3) && (argc != 3))
```

results in

```
UNSAT!
```

Meaning there is no way to reach the `assert(0)` statement.

Alternatively one may assert custom assumptions specified as smt-lib expressions
via the command line option `--precond="(assert (= RDI #x0000000000000002))"`

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

Compile both C files with:

> gcc -g -o main_1 main_1.c

and

> gcc -g -o main_2 main_2.c

One can then invoke the `wp` plugin to compare the functional
behavior of that function, using the invocation:

> bap wp --func=process_status main_1 main_2

Note that we pass in the function name we are interested in,
here `process_status`.

This gives a result including many assignments to registers and
variables in the decompiled code, which should include something along
the lines of:

```
RBP  |->  #x000000000000000
ZF   |->  #b0
RDI  |->  #x000000000000003
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

This plugin can also supplement current binary diffing tools to not
only identify code reuse between binaries but also understand the
implications and causes of their nuanced differences in behavior.

Binary diffing is the primary technique for identifying code reuse,
which is heavily used in disciplines such as malware attribution,
software plagiarism identification, and patch identification.

Current binary diffing tools only provide clues as to what is changed,
but not why or how the change manifests. For example,
[Diaphora](https://github.com/joxeankoret/diaphora) gives users percentage
scores on how closely functions between binaries match as well as how
closely the basic blocks within a function match. Those details are
helpful to identify what is changed, but most of the time, users want to
know more.

For malware attribution and software plagiarism identification, users
will want to also know if the detected similarities are authentic.
False positive identifications are not uncommon. Multiple functions
can have similar control-flow structure and instructions distribution.
For authenticity, we have to check the disassembly to see whether the
similarities are out of sheer luck, compiler-specific patterns, or
if it is actually legitimate.

For patch identification, we might not only want to identify the
specific patch but also the specific bug or vulnerability that warrants
the patch.

For all 3 cases, a certain level of program understanding is required.
With just the current binary diffing tools, the final stretch of program
understanding is left to the end users. But supplemented with the wp plugin,
the final stretch can be simplified and achieved quicker.

Below is an image showing Diaphora's diffing output for the `process_status` function:

![Process status diff](./resources/images/process_status_diff.png)

It highlights in red the basic block that differs between the two similar
functions. But if users want to understand the implications and what causes
the change, they will have to manually reason about the surrounding basic
blocks, or at worst, reason about the function's inter-procedural dependencies
like callers and callees. This pass assists users in reasoning the causes and
implications by providing register states that lead to the disparating behaviors.
The outputted register states will help answer the 'cause' question. And with
'cause' question answered, users can narrow the scope of code that they need
to analyze to understand the implications since they can be confident that
nothing else is causing those changes.

## Invocation

Information about invocation and the various options are documented in the
[CBAT Reference](https://draperlaboratory.github.io/cbat_tools/reference.html).

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

By default, logs are stored at `~/.local/state/bap`. You can change the location
of the logs by specifying the new log directory with the `--log-dir` flag or
exporting the `$BAP_LOG_DIR` environment variable.

By default, `debug` logs are not shown. To show debug logs:

    export BAP_DEBUG=true

