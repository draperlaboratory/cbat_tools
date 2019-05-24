#include <assert.h>

int bar(int x) {
  if(x < 5) {
    assert(0);
  }
  return 2;
}

int foo(int x) {
  if(x > 3) {
    bar(x);
  }
  return 1;
}

int main(int argc, char **argv) {

  foo(argc);

  return 0;
}
