#include <stdio.h>

float foo(void) {
  register float x asm ("xmm0") = 1.25;
  return x;
}

int main(int argc,char ** argv) {

  printf("%f\n", foo());

  return 0;
}
