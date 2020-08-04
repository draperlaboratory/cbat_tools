# Debruijn Explanation
This is a performance test demonstrating how `WP` verifies that 
the calculation of the index of the least significant digit is 
identical between two different implementations for 8, 16, 32,
and 64 bit integes. The naive approach (`main_2`), and the 
debruijn approach (`main_1`).

A bit of background on using de bruijn sequences: de bruijn sequences are n bit
binary strings that contain all possible `log_2 n` binary substrings exactly
once. This means that we can repurpose such a sequence as a hash function from
binary strings in the range `[0, n)` with only one bit set to numbers in the
range `[0, log_2 n]`. This hash function is perfect in the sense that for each
binary string in `x in [0,n)`, the least significant set bit of that string maps
to a unique number (the index of that bit). Recall that a perfect hash function
means that there are no collisions.

To construct this LSB hash function based on debruijn sequences and thereby
calculate the index of the least significant bit of a `n` bit integer, `k`, one
must do the following:

- isolate the least significant bit of an input number `k` by anding `k` with
  the 2s complement of `k`: `k' = k & -k`
- left shift a n bit de bruijn sequence by the least significant bit, `k'`, to
  get a unique ln n bit binary string, `k''` stored in the top `log_2 n` bits of
  the integer.
- right shift by `n - log_2 n` bits to get the unique `log_2 n` bit string,
  `k'''`
- index into a lookup table based with `k'''`. The value in this hashtable is
  the index of the LSB of the integer.

