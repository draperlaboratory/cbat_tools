#include<stdlib.h>



int main(void) {


  char * p = malloc(10);

  * (p + 3) = 0;

  return * (p + 3);

}
