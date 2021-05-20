# Loop Invariant on Stack

A `while(true)` loop that does not terminate. Since we are checking for partial
correctness, we do not check if a loop terminates. Therefore, while checking a
loop invariant, we can still get `UNSAT` with a false postcondition.

```c
int loop(void) {
  int x = 0;
  while (true) {
    x++;
  }
  return x;
}
```

## Loop Invariant Checking

The loop invariant we are checking is:

```lisp
(((address 0xb)
 (invariant "(assert true)")))

```

The loop header is at address `0xb`. You can find this address by running
`bap -dbir bin/main` to find the header node:

```
00000030:
00000036: RAX := pad:64[mem[RBP - 8, el]:u32]
00000046: #2 := low:32[RAX]
0000004a: RAX := pad:64[low:32[RAX] + 1]
0000004e: CF := low:32[RAX] < #2
00000052: OF := ~high:1[#2] & (high:1[#2] | high:1[low:32[RAX]]) &
          ~(high:1[#2] & high:1[low:32[RAX]])
00000056: AF := 0x10 = (0x10 & (low:32[RAX] ^ #2 ^ 1))
0000005a: PF :=
          ~low:1[let $1 = low:32[RAX] >> 4 ^ low:32[RAX] in
                 let $2 = $1 >> 2 ^ $1 in $2 >> 1 ^ $2]
0000005e: SF := high:1[low:32[RAX]]
00000062: ZF := 0 = low:32[RAX]
0000006b: mem := mem with [RBP - 8, el]:u32 <- low:32[RAX]
00000073: goto %00000030
```

Then with `bap -dknowledge bin/main`, you can find the corresponding address:

```
(./bin/main:0xb
  ((bap:bil-code "{
                    RAX := pad:64[mem[RBP - 8, el]:u32]
                  }")
   (bap:arch x86_64)
   (core-theory:semantics
    ((bap:ir-graph ("00000035:
                     00000036: RAX := pad:64[mem[RBP - 8, el]:u32]"))
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
     (bap:bir (%00000035))
     (bap:bil "{
                 RAX := pad:64[mem[RBP - 8, el]:u32]
               }")))
   (core-theory:label-addr (0xb))
   (core-theory:label-unit (10))
   (core-theory:encoding bap:llvm-x86_64)))
   ```

The loop invariant is just `true` in this non-terminating example. Therefore,
when we are checking the loop invariant, our constraint is `false => false`
which is equal to `true`. This would give us `UNSAT` even when the postcondition
is false.