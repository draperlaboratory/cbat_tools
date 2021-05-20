# Loop Invariant with Break

A simple loop where variables `i` and `j` are placed on the stack. The
postcondition we are verifying is `(assert (= RAX #x0000000000000003))`. This
function returns the value of `3` that is placed in the register `RAX`. This
means we exit the loop with the `break` statement. 

```c
int loop(void) {
  int i = 0;
  int j = 5;
  while (i < j) {
    if (i == 3) {
      break;
    }
    i++;
  }
  return i;
}
```

The loop invariant we are checking is:

```lisp
(((address 0x1e)
 (invariant
   "(define-fun read ((addr (_ BitVec 64))) (_ BitVec 32)
      (concat (select mem (bvadd addr #x0000000000000003))
              (select mem (bvadd addr #x0000000000000002))
              (select mem (bvadd addr #x0000000000000001))
              (select mem addr)))
    (assert
      (let ((j (read (bvsub RBP #x0000000000000004)))
            (i (read (bvsub RBP #x0000000000000008))))
      (and (bvule i #x00000003)
           (= j #x00000005))))")))
```

The loop header is at address `0x1e`. You can find this address by running
`bap -dbir bin/main` to find the header node:

```
000001d2:
000001de: RAX := pad:64[mem[RBP - 8, el]:u32]
000001ed: #2 := low:32[RAX] - mem[RBP - 4, el]:u32
000001f1: CF := low:32[RAX] < mem[RBP - 4, el]:u32
000001f5: OF := high:1[(low:32[RAX] ^ mem[RBP - 4, el]:u32) &
          (low:32[RAX] ^ #2)]
000001f9: AF := 0x10 = (0x10 & (#2 ^ low:32[RAX] ^ mem[RBP - 4, el]:u32))
000001fd: PF :=
          ~low:1[let $1 = #2 >> 4 ^ #2 in
                 let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^ $2]
00000201: SF := high:1[#2]
00000205: ZF := 0 = #2
00000210: when (SF | OF) & ~(SF & OF) goto %0000020a
0000033e: goto %00000336
```

Then with `bap -dknowledge bin/main`, you can find the corresponding address:

```
(0x1e
  ((bap:bil-code "{
                    RAX := pad:64[mem[RBP - 8, el]:u32]
                  }")
   (bap:arch x86_64)
   (core-theory:semantics
    ((bap:ir-graph ("00000046:
                     00000047: RAX := pad:64[mem[RBP - 8, el]:u32]"))
     (bap:insn-dests (()))
     (bap:insn-ops ((EAX RBP 1 Nil -8 Nil)))
     (bap:insn-asm "movl -0x8(%rbp), %eax")
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
     (bap:bir (%00000046))
     (bap:bil "{
                 RAX := pad:64[mem[RBP - 8, el]:u32]
               }")))
   (core-theory:label-addr (0x1e))
   (core-theory:label-unit (10))
   (core-theory:encoding bap:llvm-x86_64)))
   ```

The property we are checking states that `i` is the 32-bit value on the stack at
`RBP - 4`, and `j` is the 32-bit value at `RBP - 8`. `j` must be `5` and `x`
has to be less than or equal to `3`. This test should return `UNSAT`.