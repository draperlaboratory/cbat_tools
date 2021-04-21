# Notes for Solving memcpy

## Goal

Figure out how to (1) create an accurate memcpy spec and (2) ensure our code acts in a way that
specifying the spec when running memcpy code accurately changes a (2.1) SAT to UNSAT when needed
and (2.2) UNSAT to SAY when needed.

## Problems

### Regular memcpy doesn't work

memcpy from stdio.h can't be reasoned about (easily) with CBAT
since the code for memcpy is ____.
This problem was fixed by creating our own memcpy, called greg_memcpy.
This allows the memcpy to actually appear in the assembly (and bir).


### RDI, RSI and RDX not appearing on stack:

Theoretically, memcpy should take in three inputs: RDI, RSI and RDX, and should store the
contents of **RSI[0:RDX] in *RDI.
However, due to compiler optimizations and other currently-unknown reasons,
this doesn't happen exactly in the assembly (and subsequent bir)
that is produced from gcc.
One small improvement to this was to change `FILL ME IN` to `char* output malloc(3 * sizeof(char))`.
This helps because FILL ME IN. This hasn't completely solved the issue though.


## How I solved the issues:

First, I made a simple `main.asm` that ensured a value from RSI was stored in RDI and then RDI passed in RAX would work (return UNSAT) with the subroutine spec:

```
Spec: 
run () {
  bap wp \
      --func=main \
      --postcond="(assert (= RAX #x0000000000000003))" \
    --user-func-spec="greg_memcpy, (assert true), (assert (and
(= init_RSI #x0000000000000003) (= RDI init_RSI)))" \
    -- ./main
}

Code:
subroutine:
	mov rsi, rdi

main:
	call subroutine
	mov rax, rdi
	ret
```

then I did the same thing but passed the value from a register-pointer to RDI, and then to RAX, and made sure I got UNSAT again:

```
Spec: 
run () {
  bap wp \
      --func=main \
      --postcond="(assert (= ((_ extract 7 0) RAX) #x03))" \
    --user-func-spec="subroutine, (assert true), (assert (and
(= (select mem init_RSI) #x03)
(= (select mem init_RSI) ((_ extract 7 0) RDI) ) 
))" \
    -- ./main
}

Code:
subroutine:
	mov rdi, [rax]

main:
	call subroutine
	mov rax, rdi
	ret
```

Then I did the same with memcpy written in assembly:

```
```