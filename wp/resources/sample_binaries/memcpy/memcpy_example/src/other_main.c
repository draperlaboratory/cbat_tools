//Idea:
//  Tests our ability to specify the semantics of memcpy
//    using the --user-func-spec flag
//  Should return UNSAT
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

char* greg_memcpy(char *dest, const char *src, size_t n){
  char * out = dest; 
  while (n > 0){
    *dest = *src ;
    dest++;
    src++;
    n--;
  }
  return out; 
}


int main(int argc, char ** argv) {
  //char output[3];
  char* output = malloc(3 * sizeof(char)); 
  argv[0][0] = 'a';  //'a' == 0x61
  // copy contents of n1 into n2 using memcpy
  greg_memcpy(output, argv[0], 3);
  //new code
  //if (output[0] != argv[0][0]) assert(0); 
  //END new code
  // printf("%d\n",argv[0][0]);
  // printf("%d\n",output[0]);
  return output[0];
}


