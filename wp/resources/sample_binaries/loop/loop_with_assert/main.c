#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

int main(int argc, char** argv) {
  int counter = 0;
  for (int i = 0; i < 2; i++) {
    counter += 1;
  }

  if (counter == 2) {
    assert(0);
  }
  return counter;
}
