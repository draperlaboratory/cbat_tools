# Loop Invariant in Registers

A simple loop where variables `x` and `y` are placed in `RDI` and `RSI`
respectively. `x` is initialized to `0` and `y` is initialized to an arbitrary
value stored in `RDX`. Assuming that the integer stored in `RDX` is
non-negative, the postcondition we are verifying is `(assert (= RAX init_RDX))`,
or the return value of this function is equal to the initial value of `RDX`.

```c
int loop(void) {
  register int z asm ("rdx");
  register int x asm ("rdi") = 0;
  register int y asm ("rsi") = z;

  while (x < z) {
    x++;
    y--;
  }
  return x;
}
```

## No Loop Invariant

Without checking a loop invariant, WP does not know how many times we should
iterate over the while loop. Because of this, it is unable to determine that
`x` is incremented `z` times. Unrolling the loop also does not work in this
case because the the binary iterates over the loop an arbitrary number of times.
These tests should return `SAT`.

## Loop Invariant Checking

The loop invariant we are checking is:

```lisp
(((address 0x1D)
 (invariant
   "(assert
      (let ((x ((_ zero_extend 32) ((_ extract 31 0) RDI)))
            (y ((_ zero_extend 32) ((_ extract 31 0) RSI)))
            (z ((_ zero_extend 32) ((_ extract 31 0) RDX))))
      (and (= (bvadd x y) z)
           (bvule x z)
           (bvuge y #x0000000000000000))))")))

```

The loop header is at address `0x1D`. You can find this address by running
`bap -dbir bin/main` to find the header node:

```
00000044:
00000050: RCX := pad:64[low:32[RDI]]
00000059: RAX := pad:64[low:32[RDX]]
00000068: #2 := low:32[RCX] - low:32[RAX]
0000006c: CF := low:32[RCX] < low:32[RAX]
00000070: OF := high:1[(low:32[RCX] ^ low:32[RAX]) & (low:32[RCX] ^ #2)]
00000074: AF := 0x10 = (0x10 & (#2 ^ low:32[RCX] ^ low:32[RAX]))
00000078: PF :=
          ~low:1[let $1 = #2 >> 4 ^ #2 in
                 let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^ $2]
0000007c: SF := high:1[#2]
00000080: ZF := 0 = #2
0000008b: when (SF | OF) & ~(SF & OF) goto %00000085
000001d6: goto %0000010d
```

Then with `bap -dknowledge bin/main`, you can find the corresponding address:

```
(0x1d
  ((bap:bil-code "{
                    RCX := pad:64[low:32[RDI]]
                  }")
   (bap:arch x86_64)
   (core-theory:semantics
    ((bap:ir-graph ("0000004f:
                     00000050: RCX := pad:64[low:32[RDI]]"))
     (bap:insn-dests (()))
     (bap:insn-ops ((ECX EDI)))
     (bap:insn-asm "movl %edi, %ecx")
     (bap:insn-opcode MOV32rr)
     (bap:insn-properties
      ((:invalid false)
       (:jump false)
       (:cond false)
       (:indirect false)
       (:call false)
       (:return false)
       (:barrier false)
       (:affect-control-flow false)
       (:load false)
       (:store false)))
     (bap:bir (%0000004f))
     (bap:bil "{
                 RCX := pad:64[low:32[RDI]]
               }")))
   (core-theory:label-addr (0x1d))
   (core-theory:label-unit (10))
   (core-theory:encoding bap:llvm-x86_64)))
```

In the program, `x`, `y`, and `z` are placed in the bottom 32 bits of registers
`RDI`, `RSI`, and `RDX`, respectively. The loop invariant we are checking states
that `x` and `y` must be non-negative and have a sum of `z`. `x` must less than
or equal to `z` and `y` must be greater than or equal to `0`. This test should
return `UNSAT`.
