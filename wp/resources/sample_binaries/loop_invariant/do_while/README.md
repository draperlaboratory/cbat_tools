# Loop Invariant with do while Loops

A simple do while loop where variables `x` and `y` are placed on the stack. The
postcondition we are verifying is `(assert (= RAX #x0000000000000005))`. This
function returns the value of `5` that is placed in the register `RAX`.

```c
int loop(void) {
  int x = 0;
  int y = 5;

  do {
    x++;
    y--;
  } while (x < 5);

  return x;
}
```

## No Loop Invariant/Unrolling

Without unrolling the loop or checking a loop invariant, WP does not know how
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
   "(define-fun read ((addr (_ BitVec 64))) (_ BitVec 32)
      (concat (select mem (bvadd addr #x0000000000000003))
              (select mem (bvadd addr #x0000000000000002))
              (select mem (bvadd addr #x0000000000000001))
              (select mem addr)))
    (assert
      (let ((x (read (bvsub RBP #x0000000000000004)))
            (y (read (bvsub RBP #x0000000000000008))))
      (and (= (bvadd x y) #x00000005)
           (bvult x #x00000005)
           (bvuge y #x00000000))))")))
```

The loop is a single node starting at address `0x12`. This node is the target of
the back edge of the loop. You can find this address by running
`bap -dbir bin/main`:

```
00000039:
0000003f: RAX := pad:64[mem[RBP - 4, el]:u32]
0000004f: #2 := low:32[RAX]
00000053: RAX := pad:64[low:32[RAX] + 1]
...
000000b2: mem := mem with [RBP - 8, el]:u32 <- low:32[RAX]
000000c1: #8 := mem[RBP - 4, el]:u32 - 5
000000c5: CF := mem[RBP - 4, el]:u32 < 5
000000c9: OF := high:1[(mem[RBP - 4, el]:u32 ^ 5) &
          (mem[RBP - 4, el]:u32 ^ #8)]
000000cd: AF := 0x10 = (0x10 & (#8 ^ mem[RBP - 4, el]:u32 ^ 5))
000000d1: PF :=
          ~low:1[let $1 = #8 >> 4 ^ #8 in
                 let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^ $2]
000000d5: SF := high:1[#8]
000000d9: ZF := 0 = #8
000000e3: when (SF | OF) & ~(SF & OF) goto %00000039
00000213: goto %000000ea
```

Then with `bap -dknowledge bin/main`, you can find the corresponding address:

```
(0x12
  ((bap:bil-code "{
                    RAX := pad:64[mem[RBP - 4, el]:u32]
                  }")
   (bap:arch x86_64)
   (core-theory:semantics
    ((bap:ir-graph ("0000003e:
                     0000003f: RAX := pad:64[mem[RBP - 4, el]:u32]"))
     (bap:insn-dests (()))
     (bap:insn-ops ((EAX RBP 1 Nil -4 Nil)))
     (bap:insn-asm "movl -0x4(%rbp), %eax")
     (bap:insn-opcode MOV32rm)
     (bap:insn-properties
      ((:invalid false)
       (:jump false)
       (:cond false)
       (:indirect false)
       (:call false)
       (:return false)
       (:barrier false)
       (:affect-control-flow false)
       (:load true)
       (:store false)))
     (bap:bir (%0000003e))
     (bap:bil "{
                 RAX := pad:64[mem[RBP - 4, el]:u32]
               }")))
   (core-theory:label-addr (0x12))
   (core-theory:label-unit (10))
   (core-theory:encoding bap:llvm-x86_64)))
   ```

The property we are checking states that `x` is the 32-bit value on the stack at
`RBP - 4`, and `y` is the 32-bit value at `RBP - 8`. `x` and `y` must be
non-negative and have a sum of `5`. `x` must less than `5` and `y`
must be greater than or equal to `0`.

The reason why this invariant states `x < 5` rather than `x <= 5` from the
`while loop` example is because the first iteration of the loop is always
executed. If `x` were to be `5` at the beginning of the loop, the loop invariant
would not hold after the first iteration (`x` would become `6`). This test
should return `UNSAT`.
