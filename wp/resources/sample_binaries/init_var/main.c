#include <stdint.h>

uint64_t foo(uint64_t x) {
  return x + 1;
}

int main(int argc,char ** argv) {

  foo(argc);

  return 0;
}
