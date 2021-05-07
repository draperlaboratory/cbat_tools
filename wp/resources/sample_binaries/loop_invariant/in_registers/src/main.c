#include <assert.h>

int loop(void) {
  register int x asm ("rdi") = 0;
  register int y asm ("rsi") = 5;
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
