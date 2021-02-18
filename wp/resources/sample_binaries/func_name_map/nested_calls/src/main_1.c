#include <stdlib.h>
#include <stdio.h>

int bar(int x) {
  return x + 1;
}

int foo(int x) {
  return x + bar(x);
}
