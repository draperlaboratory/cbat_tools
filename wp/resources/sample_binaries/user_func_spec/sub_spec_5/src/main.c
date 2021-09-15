//  Tests that our code sees and uses f and g's specs
#include <assert.h>

int g() {
  return 0x0000000000000067;
}
int f() {
  return 0x0000000000000067;
}

int main(int argc, char ** argv) {
  if (f() == 0x0000000000000067) assert(0);
  if (g() == 0x0000000000000067) assert(0);  
  return argc;
}
