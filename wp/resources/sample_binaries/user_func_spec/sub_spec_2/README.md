A basic C example that tests subroutine constraints where the constraint
can determine whether or not an assert_fail is possible for the given C code.

For example, in the code

```
int main(int argc,char ** argv) {
  argc = g();
  if (argc == 0x0000000000000067) assert(0);
  return argc;
}
```

If we want an UNSAT with the trip-assert flag on,
we need to show `argc` can't be 0x67.
If a postcondition for g says `(assert not(= RAX 0x67))`,
then we can be assured an UNSAT. 
