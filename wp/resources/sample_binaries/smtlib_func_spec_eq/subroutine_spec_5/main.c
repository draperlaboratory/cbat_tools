//This test is to uniquely track RAX and RDI.
//This should return SAT, since RDI needs to be 1 specifically to
  // make the constriaints in run_wp.sh work

#include <stdlib.h>

// a = RDI
// b = RaX

// pre : (a = 5)
int g(int a) {
  a = 7;
  return (7 * 5); 
}
// post : (b = a' * a)

// should work just when a = 1
// (4 + 1 = 5) /\ (4 + 1 = a'_yz) =>  (b_z() = a'_yz * a_z) => (b_z() = a'_z * a_z * 5))
int main (int a) {
  // (4 + 1 = 5) /\ (4 + 1 = a'_yz) =>  (b_z() = a'_yz * a_z) => (b_z() = a'_z * a_z * 5))
  a = 4 ;
  // (a + 1 = 5) /\ (4 + 1 = a'_yz) =>  (b_z() = a'_yz * a_z) => (b_z() = a'_z * a_z * 5))
  a = a + 1 ;
  // (a = 5) /\ (a = a'_yz) =>  (b_z() = a'_yz * a_z) => (b_z() = a'_z * a_z * 5))
  //
  //     ^ which turns into ^
  //
  // (a = 5) /\ (b_y() = a'_y[5] * a_y[7]) => (b[35] =  a'[1] * a[7]  * 5))
  //
  // change Q_g from (b = a' * a) to (b_y() = a'_y * a_y)
  return g(a);
 }
// post : (b = a' * a * 5)
