float foo(void) {
  register float x asm ("xmm0") = 2.0;
  register float y asm ("xmm1") = 3.0;
  return x + y;
}

int main(int argc,char ** argv) {

  foo();

  return 0;
}
