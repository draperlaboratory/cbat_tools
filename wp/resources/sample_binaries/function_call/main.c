#include <assert.h>

int foo(int x) {
  if(x == 5) {
    assert(0);
  }

  return 1;
}

int main(int argc, char **argv) {

  foo(argc);

  return 0;
}
