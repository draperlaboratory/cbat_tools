# Specification Summary:

Before attempting to understand `run_wp.sh`, please read `memcpy_example/README.md` first.

This spec is identical to `memcpy_example/run_wp.sh` with one new added piece.
We now reason over some section of memory other than `[RDI]`.
We assume memory location `#x701050` equals `12` before `main` runs
and we want to assure `#x701050` is unchanged after `main` runs.
Part ii. of the `memcpy`-postcondition (see `memcpy_example/README.md`) is now needed to ensure memory locations outside `[RDI]` are preserved.
The location `#x701050` was chosen because it is sufficiently arbitrary
and far enough away from other registers so that it is easy to reason about.

In the precondition to `main`, the upper-bound on `RDI` is reduced to `0xFFFF` from `0xFFFFFFFF`
to reduce the time needed for running the test.
However, the example should still work for when the upper-bound is `0xFFFFFFFF`.