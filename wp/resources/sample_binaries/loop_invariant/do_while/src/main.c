#include <assert.h>

int loop(void) {
  int x = 0;
  int y = 5;

  do {
    x++;
    y--;
  } while (x < 5);

  return x;
}

int main(int argc, char **argv) {

  loop();

  return 0;
}
