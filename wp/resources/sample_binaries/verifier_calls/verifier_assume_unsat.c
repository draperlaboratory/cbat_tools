#include "../../../plugin/api/c/cbat.h"

void
main(void)
{
  int x;
  __VERIFIER_assume(x > 0);

  if(x <= 0) {
    __VERIFIER_error();
  }
}
