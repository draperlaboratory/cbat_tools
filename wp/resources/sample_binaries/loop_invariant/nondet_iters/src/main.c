#include <assert.h>

int loop(void) {
  register int z asm ("rdx");
  register int x asm ("rdi") = 0;
  register int y asm ("rsi") = z;

  while (x < z) {
    x++;
    y--;
  }
  return x;
}

int main(int argc, char **argv) {
  loop();
  return 0;
}
