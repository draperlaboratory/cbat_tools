#include <stdint.h>
#include <stdlib.h>

int8_t init(){
  return 1;
}

int8_t example(){
  int8_t err = init();
  return err;
}
