//Idea:
//  We know  want to see if main_2.c and main_1.c
//  are equivalent. If we can use {x =/= 2} foo(x) {result = x},
//  then the show that main_1 = main_2 when x =/= 2.

#include <stdlib.h>

int foo(int x) {
  if(x == 2) {
    return 42;
  }
  return x;
}

int main(int argc, char *argv[]) {
  argc = foo(argc);
  return argc;
}
