//Idea:
//  We're have different versions of g that do different things (+4 or +8) in
//  the two programs, and show that we can give them different funtion summaries
//  and prove that main gets the same result in both cases (because it calls g
//  with different arguments).


#include <stdlib.h>

// pre : (true)
int g(int x) {
  return x+8;
}
// post : (RAX = init_RDI+8)


int main(int argc, char ** argv) {
  int z = 6;
  return g(z);
}
// post : (RAX = 14)
