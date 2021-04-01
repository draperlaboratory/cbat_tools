#include <stdlib.h>

unsigned int foo[10];

unsigned int foo_get(int x) {
  return foo[x + 1];
}

int main(void) {

  return 0;

}
