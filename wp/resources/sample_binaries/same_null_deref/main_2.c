#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>

bool null_deref(int x, int y) {
  int * null = 0x0;
  if (*null) {
    return x + y;
  }
  return x + y;
}

int main(int argc, char ** argv) {
  return 0;
}
