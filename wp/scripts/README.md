# WP Run Scripts

## Usage

These scripts are for running WP on two binaries. `run.bash` will compare all
subroutines that are found in both binaries, and `run_single.bash` is used for
analyzing a single subroutine specified by the user.

### View help

```
bash run.bash --help
```

### Run WP on all subroutines between two binaries

This runs WP to compare all subroutines between two binaries.
  1. Compare all subs with default settings that compare post callee-saved
     register values.
  2. Compare all subs with rewrite-addresses on.
  3. Compare all subs with rewrite-addresses and check-invalid-derefs on.

It prints out the number of SATs, UNSATs, and UNKNOWNs (timeouts), and stores
the results of each subroutine in the output directory.

Usage:
```
bash run.bash [-j|--jobs] [-t|--timeout] [-o|--output] -- <original> <modified>
```
	- jobs: How many jobs to run in parallel (default: 1)
	- timeout: Timeout for each job (default: 1000s)
	- output: Location of logs and results of each subroutine
	          (default: output-<date>)

The default settings are:
```
bap wp \
  --no-byteweight \
  --function=<function> \
  --num-unroll=0 \
  --show=bir,paths \
  --compare-post-reg-values=R12,R13,R14,R15,RBX,RSP,RBP,RAX \
  <original> <modified>
```

Each iteration of WP will run new options on the SATs and UNKNOWNs from the
previous results.

### Test WP on a single function

```
bash run_single.bash --function <function> <original> <modified>
```

This script is for running WP on a single function specified by the user using
the default settings above. It also displays the runtime of the analysis. This
script is useful for looking at individual cases found by the `run.bash` script.
