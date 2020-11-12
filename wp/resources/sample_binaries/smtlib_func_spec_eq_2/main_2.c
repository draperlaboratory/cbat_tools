//Idea:
//  We know  want to see if main_2.c and main_1.c
//  are equivalent. If we can use {x >= 4} foo(x) {result = x},
//  then the show that main_1 = main_2 when x >= 4.

#include <stdlib.h>

int foo(int x) {
  if(x == 2) {
    return 42;
  }
  return x;
}

int main(int argc, char *argv[]) {
  if (argc < 4) return argc ;
  argc = foo(argc);
  return argc;
}

// Make C code (this code!) 
// Take SMTLIB stuff, pass it into mk_env
  // Specifically part of handler
// Look where we define built in summaries from the subroutines
  // There are some functions that have specific summaries in precondition.ml
    // spec_verifier_error and spec_verifier_assume
    // fun_spec turns a postcondition into a precondition
    // spec_verifier_error and spec_verifier_assume return fun_spec option's
       // They do this by grabbing a spec : specs:(Bap.Std.Sub.t -> Bap.Std.Arch.t -> fun_spec option) list
         // from a list of specs and continue the procedure from there. (Usually a contant in the past.)
