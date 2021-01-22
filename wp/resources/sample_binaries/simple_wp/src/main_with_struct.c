#include <stdio.h>
#include <assert.h>


/* typedef struct bar { int foo; } bar_t; */

/* int foo(bar_t * baz) { */

/*   int x = baz -> foo; */
  
/*   if(baz->foo == 10) */
/*     assert(0); */
  
/*   return 0; */

/* } */



int main(int argc,char ** argv) {

  /* printf("%lu\n", sizeof(bar_t)); */
  
  if(2*argc+3 == 135)
    assert(0);
  
  
  return 0;
}
