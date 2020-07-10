#include <stdlib.h>

int main() {
  int *addr = malloc(sizeof(int));
  *addr = 42;

  int *addr2 = malloc(sizeof(int));
  *addr2 = 68;
}
