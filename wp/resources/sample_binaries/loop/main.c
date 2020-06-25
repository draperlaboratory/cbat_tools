#include <assert.h>

int main(int argc, char** argv) {
  int counter = 0;
  int i = 0;
  for (int i = 0; i < 5; i++) {
    counter += 1;
  }
  /* if (i < 5) { */
  /*   i ++; */
  /*   counter += 1; */
  /* } */
  /* if (i < 5) { */
  /*   i ++; */
  /*   counter += 1; */
  /* } */
  /* if (i < 5) { */
  /*   i ++; */
  /*   counter += 1; */
  /* } */
  /* if (i < 5) { */
  /*   i ++; */
  /*   counter += 1; */
  /* } */
  /* if (i < 5) { */
  /*   i ++; */
  /*   counter += 1; */
  /* } */
  /* if (i < 5) { */
  /*   i ++; */
  /*   counter += 1; */
  /* } */

  assert(counter < 5);
  return counter;
}
