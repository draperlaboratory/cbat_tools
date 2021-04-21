//Idea:
//  Tests our ability to specify the semantics of memcpy
//    using the --user-func-spec flag
//  Should return UNSAT
#include <assert.h>
#include <stdlib.h>
#include <string.h>

typedef struct node{
  unsigned int size : 10;
  struct node * next;
} node_t;


int main(int argc,char ** argv) {
  node_t n = {.size = 0x0000000000000042, .next = NULL};
  node_t n2;
  // copy contents of n1 into n2 using memcpy
  memcpy(&n2,&n,size_of(node_t));
  argc = g();
  return n2.size;
}
// postcondition could be something like
// (assert (= RAX #x0000000000000042))
