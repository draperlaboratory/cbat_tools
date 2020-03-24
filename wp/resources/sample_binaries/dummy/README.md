This directory contains a simple hello_world dummy binary.

Currently, in WP's comparison analysis, the two binaries are passed in with the
flags file1 and file2. However, a binary still needs to be passed into BAP.
We use this dummy binary for this purpose.

For example:
```
bap --pass=wp \
  --wp-file1=file1.bpj \
  --wp-file2=file2.bpj \
  --wp-compare \
  hello_word.out
```
