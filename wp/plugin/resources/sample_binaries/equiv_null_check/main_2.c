#include<stdlib.h>
#include<assert.h>


int main(void) {


  char * p = malloc(10);

  if( p == NULL ) assert(0);
  
  * (p + 3) = 0;

  return * (p + 3);

}
