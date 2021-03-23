#include <assert.h>

int loop(void) {
  int x = 0;
  int y = 5;
  while (x < 5) {
    x++;
    y--;
  }
  return x;
}

int main(int argc, char **argv) {

  loop();

  return 0;
}
