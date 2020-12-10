//Idea:
//  Tests that our code sees and uses g's pre and post-conditions.
//  Should return UNSAT
#include <assert.h>
#include <stdlib.h>

// pre : (true)
int g() {
  return 0x0000000000000067;
}
// post : (RAX = 4)


int main(int argc) {
  argc = g();
  if (argc == 0x0000000000000067) assert(0);
  return argc;
}
// post : (RAX = 3)
