# Specification Summary:

This spec asserts that `RAX == 0x0` after running `main`, i.e. `main` returns `0x0`.
 The function `main` only returns `0x0` if `memcpy` copies the contents from one struct instance
 (the source called `account` and second input to `memcpy`) into another (the destination called `account_copy` and first input to `memcpy`).
 Thus the specification must give an accurate description of `memcpy` in order to return `UNSAT`.

## `main` specs: 
  - `main` precondition: Assert `RAX == 0x0` (which means the `memcpy` function worked as expected)
  - `main` precondition: Assert `0x4 <= RDI <= 0xFFFFFFFF`.
  The lower bound insures `RDI` is big enough to be used to copy the 4 bytes of the struct from the source to the destination.
  The user can test this by changing the struct in `main.c` to `short balance;`,
  whereby the lower bound can be reduced to `0x2` while still getting `UNSAT`.
  The upper bound is needed for reasons concerning how `RDI` is stored in memory,
  where only the bottom 32-bits are copied to memory in the bir of main. 

## `memcpy` specs:
  - `memcpy` precondition : Assert `true` (i.e. don't assert anything)
  - `memcpy` postcondition : Assert
    1. `RDI` remains unchanged
    2. All memory outside of `[RDI]` is unchanged
    3. `[RSI]` (the source) before `memcpy` equals `[RDI]` (the destination) after `memcpy`

Note that if [RSI] and [RDI] overlap, the behavior is undefined.
For this specific example, removing i. or iii. will render a `SAT`, but removing ii. won't,
since this example doesn't worry about memory outside of `[RDI]` after `memcpy` is called.
We include ii. still because it gives the complete specification of `memcpy`.
To see an example where ii. is needed, see `memcpy_example_2/run_wp.sh`.

