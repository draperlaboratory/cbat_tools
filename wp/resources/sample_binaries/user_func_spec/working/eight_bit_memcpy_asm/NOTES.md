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

