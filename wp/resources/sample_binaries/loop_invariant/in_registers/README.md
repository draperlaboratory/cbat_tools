# Loop Invariant in Registers

A simple loop where variables `x` and `y` are placed in `rdi` and `rsi`
respectively. The postcondition we are verifying is
`(assert (= RAX #x0000000000000005))`. This function returns the value of `5`
that is placed in the register `RAX`. 

```c
int loop(void) {
  register int x asm ("rdi") = 0;
  register int y asm ("rsi") = 5;
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
(((address 0x1E)
 (invariant
   "(assert
      (let ((x ((_ zero_extend 32) ((_ extract 31 0) RDI)))
            (y ((_ zero_extend 32) ((_ extract 31 0) RSI))))
      (and (= (bvadd x y) #x0000000000000005)
           (bvule x #x0000000000000005)
           (bvuge y #x0000000000000000))))")))
```

The loop header is at address `0x1E`. You can find this address by running
`bap -dbir bin/main` to find the header node:

```
0000003b:
00000047: RAX := pad:64[low:32[RDI]]
00000056: #2 := low:32[RAX] - 4
0000005a: CF := low:32[RAX] < 4
0000005e: OF := high:1[(low:32[RAX] ^ 4) & (low:32[RAX] ^ #2)]
00000062: AF := 0x10 = (0x10 & (#2 ^ low:32[RAX] ^ 4))
00000066: PF :=
          ~low:1[let $1 = #2 >> 4 ^ #2 in
                 let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^ $2]
0000006a: SF := high:1[#2]
0000006e: ZF := 0 = #2
00000079: when ZF | (SF | OF) & ~(SF & OF) goto %00000073
000001c0: goto %000000fb
```

Then with `bap -dknowledge bin/main`, you can find the corresponding address:

```
(0x1e
  ((bap:bil-code "{
                    RAX := pad:64[low:32[RDI]]
                  }")
   (bap:arch x86_64)
   (core-theory:semantics
    ((bap:ir-graph ("00000046:
                     00000047: RAX := pad:64[low:32[RDI]]"))
     (bap:insn-dests (()))
     (bap:insn-ops ((EAX EDI)))
     (bap:insn-asm "movl %edi, %eax")
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
     (bap:bir (%00000046))
     (bap:bil "{
                 RAX := pad:64[low:32[RDI]]
               }")))
   (core-theory:label-addr (0x1e))
   (core-theory:label-unit (10))
   (core-theory:encoding bap:llvm-x86_64)))
   ```

In the program, `x` and `y` are placed in the bottom 32 bits of registers `RDI`
and `RSI` respectively. The property we are checking states that `x` and `y`
must be non-negative and have a sum of `5`. `x` must less than or equal to `5`
and `y` must be greater than or equal to `0`. This test should return `UNSAT`.