# Loop Invariant on Stack

A simple loop where variables `x` and `y` are placed on the stack. The
postcondition we are verifying is `(assert (= RAX #x0000000000000005))`. This
function returns the value of `5` that is placed in the register `RAX`. 

```c
int loop(void) {
  int x = 0;
  int y = 5;
  while (x < 5) {
    x++;
    y--;
  }
  return x;
}
```

## No Loop Invariant/Unrolling

Without a unrolling the loop or checking a loop invariant, WP does not know how
many times we should iterate over the while loop. Because of this, it is unable
to determine that `x` is `5` at the end of the function. This test should return
`SAT`.

## Loop Unrolling

If we unroll the loop at least `4` times, WP will know that `x` is incremented
`5` times, and will be able to prove that `x` is `5` at the end of the function.
This test should return `UNSAT`.

## Loop Invariant Checking

The loop invariant we are checking is:

```lisp
(((address 0x12)
 (invariant
   "(define-fun read ((addr (_ BitVec 64))) (_ BitVec 8)
      (select mem (bvadd addr RBP)))
    (define-fun stack_read ((addr (_ BitVec 64))) (_ BitVec 32)
      (concat (read addr)
              (read (bvsub addr #x0000000000000001))
              (read (bvsub addr #x0000000000000002))
              (read (bvsub addr #x0000000000000003))))
    (assert
      (let ((x (stack_read #xffffffffffffffff))
            (y (stack_read #xfffffffffffffffb)))
      (and (= (bvadd x y) #x00000005)
           (bvule x #x00000005)
           (bvuge y #x00000000))))")))
```

The loop header is at address `0x12`. You can find this address by running
`bap -dbir bin/main` to find the header node:

```
00000039:
00000045: #2 := mem[RBP - 4, el]:u32 - 5
00000049: CF := mem[RBP - 4, el]:u32 < 5
0000004d: OF := high:1[(mem[RBP - 4, el]:u32 ^ 5) &
          (mem[RBP - 4, el]:u32 ^ #2)]
00000051: AF := 0x10 = (0x10 & (#2 ^ mem[RBP - 4, el]:u32 ^ 5))
00000055: PF :=
          ~low:1[let $1 = #2 >> 4 ^ #2 in
                 let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^ $2]
00000059: SF := high:1[#2]
0000005d: ZF := 0 = #2
00000068: when ~((SF | OF) & ~(SF & OF)) goto %00000062
0000021e: goto %00000195
```

Then with `bap -dknowledge bin/main`, you can find the corresponding address:

```
(0x12
  ((bap:bil-code
    "{
       #2 := mem[RBP - 4, el]:u32 - 5
       CF := mem[RBP - 4, el]:u32 < 5
       OF := high:1[(mem[RBP - 4, el]:u32 ^ 5) & (mem[RBP - 4, el]:u32 ^ #2)]
       AF := 0x10 = (0x10 & (#2 ^ mem[RBP - 4, el]:u32 ^ 5))
       PF :=
         ~low:1[let $1 = #2 >> 4 ^ #2 in let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^
     $2]
       SF := high:1[#2]
       ZF := 0 = #2
     }")
   ...
   (core-theory:label-addr (0x12))
   (core-theory:label-unit (10))
   (core-theory:encoding bap:llvm-x86_64)))
   ```

The property we are checking states that `x` is the 32-bit value on the stack at
`RBP - 4`, and `y` is the 32-bit value at `RBP - 8`. `x` and `y` must be
non-negative and have a sum of `5`. `x` must less than or equal to `5` and `y`
must be greater than or equal to `0`. This test should return `UNSAT`.