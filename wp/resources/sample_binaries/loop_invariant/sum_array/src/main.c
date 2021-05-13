#include <stdint.h>
#include <stdio.h>


uint8_t sum(uint8_t length, uint8_t* array) {
  uint8_t n = 0;
  uint8_t total = 0;
  while(n < length) {
    total += array[n++];
  }
  return total;
}

int main(int argc, char **argv) {
  uint8_t array[5] = {0, 20, 2, 10, 10};
  uint32_t fortytwo = sum(5,array);
  printf("Should be 42: %d\n", fortytwo);
  return 0;
}
