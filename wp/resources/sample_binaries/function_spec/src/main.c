#include <assert.h>

int foo(int x) {
  return 3;
}

int main(int argc, char **argv) {

  if(foo(argc) == 5){
    assert(0);
  }

  return 0;
}
