#include <assert.h>
#include <stdlib.h>

int g() {
  return 0x0000000000000067;
}

int main(int argc,char ** argv) {
  argc = g();
  int x = g(); 
  return x ;
}
