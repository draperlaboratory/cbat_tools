//Idea:
//  Tests that our code sees and uses g's pre and post-conditions.
//  Should return UNSAT

#include <stdlib.h>

// pre : (true)
int g() {
  return 4;
}
// post : (RAX = 4)


int main(int argc) {
  return g();
}
// post : (RAX = 3)
