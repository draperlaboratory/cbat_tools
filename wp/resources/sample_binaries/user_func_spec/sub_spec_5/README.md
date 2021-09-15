A basic C example that tests multiple subroutine specs simultaneously.

For example, in the code

```
int main(int argc,char ** argv) {
  if (f() == 0x0000000000000067) assert(0);
  if (g() == 0x0000000000000067) assert(0);  
  return argc;
}
```

If we want an UNSAT with the trip-assert flag on,
we need to show that neither `f` or `g` can return `67`.
If a postcondition for f and g says `(assert not(= RAX 0x67))`,
then we can be assured an UNSAT. 
