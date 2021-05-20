#include <stdio.h>

int loop(void) {
  int i = 0;
  int j = 5;
  while (i < j) {
    if (i == 3) {
      break;
    }
    i++;
  }
  return i;
}

int main(int argc, char **argv) {
  return loop();
}
