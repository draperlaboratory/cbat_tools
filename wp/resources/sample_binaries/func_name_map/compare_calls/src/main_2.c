#include <stdlib.h>
#include <stdio.h>

int test_bar(int x) {
  return x + 1;
}

int test_baz(int x) {
  return x + 2;
}

int test_foo(int x) {
  return test_bar(x) + test_baz(x);
}
