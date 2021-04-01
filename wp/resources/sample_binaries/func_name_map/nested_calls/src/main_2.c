#include <stdlib.h>
#include <stdio.h>

int test_bar(int x) {
  return x + 2;
}

int test_foo(int x) {
  return x + test_bar(x);
}
