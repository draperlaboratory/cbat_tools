#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

int foo(uint8_t i){
  int j = 0;
  while(j < 3){
    j++;
    while(j < 3){
      j++;
    }
  }
  printf("\nVALUE: %x\n", j);
  return j ;
}

int main(int argc, char** argv) {
  foo(5);
  return 0;
}
