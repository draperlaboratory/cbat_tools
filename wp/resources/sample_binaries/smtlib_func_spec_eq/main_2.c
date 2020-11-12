//Idea:
//  We know  want to see if main_2.c and main_1.c
//  are equivalent. If we can use {x >= 4} foo(x) {result = x},
//  then the show that main_1 = main_2 when x >= 4.

#include <stdlib.h>

int foo(int x) {
  if(x == 7) {
    return 7;
  }
  return 4;
}

int main(int argc, char *argv[]) {
  if (argc < 4) return 4 ;
  argc = foo(argc);
  return argc;
}
