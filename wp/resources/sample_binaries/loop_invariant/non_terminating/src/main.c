#include <stdbool.h>

int loop(void) {
  int x = 0;
  while (true) {
    x++;
  }
  return x;
}

int main(int argc, char **argv) {

  loop();

  return 0;
}
