#include <assert.h>
#include <stdlib.h>
#include "../../../../plugin/api/c/cbat.h"

#define STRING_MAX 10

char * my_string_alloc(int size){
  return (char *) __VERIFIER_nondet_long ();
}

int main(int argc, char* argv[])
{
  char *string1, *string2;
  string1 = my_string_alloc(STRING_MAX);
  string2 = my_string_alloc(STRING_MAX);

  if ( !(string2) )
    goto gotoExample_string2;

  //important code goes here
  assert(string1 && string2);

gotoExample_string2:
  free(string2);
gotoExample_string1:
  free(string1);

  return 0;
}
