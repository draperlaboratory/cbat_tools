#include <stdlib.h>
#include <stdio.h>

int bar(int x) {
  return x + 1;
}

int baz(int x) {
  return x + 2;
}

int foo(int x) {
  return bar(x);
}
