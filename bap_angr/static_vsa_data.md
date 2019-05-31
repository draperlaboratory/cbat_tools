# Static VSA data

These are the results we collected for our static VSA tests.
We ran our `angr` and `bap` VSA analyses on 6 toy programs.


## Summarized data

Here is a summary of the data.

The BAP and angr time is the average user (CPU) 
time in seconds. Elapsed (wall clock) time is
not significantly greater.

The RSS numbers are the average maximum resident 
set size in kilobytes (with page size being the 
standard 4096 bytes).

Note:

* The first row shows shows the average time and 
  max RSS that BAP and angr use to load an empty 
  program as a project.
* angr cannot complete its analysis of the 
  `reg_jump` program due to a bug we were not 
  able to track down.
* BAP cannot complete its analysis of the `simple_call`
  program, because it encounters an edge explosion 
  there. Our plugin is designed to stop-and-exit 
  if it encounters this.

Here are the results:

    ---------------------------------------------------------------------------------------------
    | Exe             | BAP time  | angr time  | BAP RSS  | angr RSS  | BAP found  | angr found |
    ---------------------------------------------------------------------------------------------
    | empty           | 0.51      | 0.91       | 83879    | 82366     | n/a        | n/a        |
    | reg_jump        | 0.71      | ---        | 124232   | ---       | 8/8 (100%) | ---        |
    | short_jump      | 0.73      | 1.21       | 124359   | 88263     | 5/5 (100%) | 4/5 (80%)  |
    | torture         | 0.72      | 1.59       | 124456   | 91352     | 8/8 (100%) | 7/8 (88%)  |
    | torture_swapped | 0.71      | 1.85       | 124408   | 93986     | 8/8 (100%) | 7/8 (88%)  |
    | jump_bomb       | 0.70      | 4.20       | 124250   | 104188    | 8/8 (100%) | 8/8 (100%) |
    | simple_call     | ---       | 6.72       | ---      | 121923    | ??         | ??         |
    ---------------------------------------------------------------------------------------------

We also run these analyses with pypy. The following
table compares the average running time and max RSS 
of python and PyPy:

    -------------------------------------------------------------------
    | Exe             | pyth time | pypy time  | pyth RSS | pypy RSS  |
    -------------------------------------------------------------------
    | empty           | 0.91      | 1.84       | 82366    | 142814    |
    | reg_jump        | ---       | ---        | ---      | ---       |
    | short_jump      | 1.21      | 2.81       | 88263    | 157212    |
    | torture         | 1.59      | 3.96       | 91352    | 165492    |
    | torture_swapped | 1.85      | 4.58       | 93986    | 171370    |
    | jump_bomb       | 4.20      | 7.87       | 104188   | 196528    |
    | simple_call     | 6.72      | 6.16       | 121923   | 198112    |
    -------------------------------------------------------------------

This suggests that `pypy` is less efficient for 
small programs, but it gets better for large programs.

The details behind these summary results can be found 
in the rest of this document.


## Binary programs mappings/rename

For the paper, we renamed the toy programs in this way:

* `short_jump` was `arith_reg_jump_short`
* `jump_bomb` was `jump_bomb`
* `reg_jump` was `vsa_arith_register_jump`
* `torture` was `vsa_edges_torture`
* `swapped` was `vsa_edges_torture_swapped`
* `simple_call` was `simple_arithmetica_function_call`


## Measurements

When we run a VSA, we measure the following points:

* User (CPU) time - seconds
* Wall (elapsed) time - seconds
* RSS (max resident set size) - bytes (page size is 4096 bytes)

Each of these points are collected for 5 runs, then each is averaged.


## Angr (regular python 2.7)

### empty project

This is an `angr` analysis that does nothing but 
load an empty program into a project. The empty 
program  imports `stdlib.h` and `stdio.h`, and 
contains an empty `main` function.

This tells us the resources that `angr` needs, 
just to load up.

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.89      | 0.95      | 82292   |
    | 0.94      | 1.01      | 82592   |
    | 0.92      | 0.95      | 82340   |
    | 0.90      | 0.94      | 82340   |
    | 0.92      | 0.94      | 82268   |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.91      | 0.96      | 82366   |
    -----------------------------------


### arith_register_jump (reg_jump)

No data. Script won't complete. Gets stuck on printing something.


### arith_reg_jump_short (short_jump)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.16      | 1.26      | 88176   |
    | 1.25      | 1.29      | 88256   |
    | 1.20      | 1.24      | 88412   |
    | 1.20      | 1.27      | 88321   |
    | 1.24      | 1.26      | 88152   |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.21      | 1.26      | 88263   |
    -----------------------------------



### edges_torture (torture)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.61      | 1.64      | 91420   |
    | 1.52      | 1.61      | 91264   |
    | 1.60      | 1.64      | 91464   |
    | 1.64      | 1.70      | 91256   | 
    | 1.59      | 1.67      | 91356   |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.59      | 1.65      | 91352   |
    -----------------------------------


### edges_torture_swapped (swapped)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.86      | 1.93      | 93932   |
    | 1.84      | 1.95      | 94096   |
    | 1.87      | 1.97      | 93952   |
    | 1.81      | 1.90      | 93852   | 
    | 1.86      | 1.95      | 94096   |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.85      | 1.94      | 93986   |
    -----------------------------------


### jump_bomb (jump_bomb)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 4.14      | 4.24      | 104123  |
    | 4.28      | 4.35      | 104216  |
    | 4.15      | 4.26      | 104220  |
    | 4.20      | 4.27      | 104152  | 
    | 4.24      | 4.33      | 104228  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 4.20      | 4.29      | 104188  |
    -----------------------------------


### simple_arithmetic_function_call (simple_call)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 6.66      | 6.75      | 122060  |
    | 6.68      | 6.81      | 121832  |
    | 6.84      | 6.96      | 121804  |
    | 6.78      | 6.84      | 122052  | 
    | 6.63      | 6.76      | 121868  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 6.72      | 6.82      | 121923  |
    -----------------------------------


## BAP

BAP caches the entire disassembly, and some passes
cache their results too. See `bap --cache-help`.
For the results below, we always ran bap with
the `--no-cache` flag. The performance gets
significantly faster if you utilize the caching.
For example, the running time for all analyses
below dips below a half second.



### loading an empty project

This is a BAP plugin that does nothing but load an 
empty program into a project. The empty program 
imports `stdlib.h` and `stdio.h`, and contains
an empty `main` function.

This tells us the resources that BAP needs, 
just to load up.

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.52      | 0.61      | 83812   |
    | 0.50      | 0.63      | 83872   |
    | 0.52      | 0.62      | 84004   |
    | 0.49      | 0.61      | 84024   |
    | 0.53      | 0.62      | 83684   |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.51      | 0.62      | 83879   |
    -----------------------------------


### arith_register_jump (reg_jump)

Note that the `angr` version of this doesn't complete.

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.72      | 0.91      | 124316  |
    | 0.71      | 0.87      | 124264  |
    | 0.72      | 0.88      | 124084  |
    | 0.70      | 0.87      | 124096  |
    | 0.69      | 0.87      | 124400  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.71      | 0.88      | 124232  |
    -----------------------------------


### arith_reg_jump_short (short_jump)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.81      | 0.91      | 124956  |
    | 0.72      | 0.87      | 123876  |
    | 0.70      | 0.86      | 124364  |
    | 0.74      | 0.88      | 124368  |
    | 0.66      | 0.86      | 124232  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.73      | 0.88      | 124359  |
    -----------------------------------



### edges_torture (torture)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.73      | 0.91      | 125224  |
    | 0.72      | 0.87      | 124144  |
    | 0.74      | 0.87      | 124364  |
    | 0.73      | 0.88      | 124136  | 
    | 0.66      | 0.86      | 124412  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.72      | 0.88      | 124456  |
    -----------------------------------


### edges_torture_swapped (swapped)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.76      | 0.92      | 125264  |
    | 0.70      | 0.88      | 124260  |
    | 0.69      | 0.86      | 124192  |
    | 0.72      | 0.86      | 124168  | 
    | 0.70      | 0.87      | 124156  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.71      | 0.88      | 124408  |
    -----------------------------------


### jump_bomb (jump_bomb)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.68      | 0.86      | 124152  |
    | 0.69      | 0.85      | 124352  |
    | 0.70      | 0.86      | 124320  |
    | 0.72      | 0.86      | 124348  | 
    | 0.72      | 0.87      | 124080  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 0.70      | 0.86      | 124250  |
    -----------------------------------


### simple_arithmetic_function_call (simple_call)

BAP encounters an edge explosion here and stops.


## Angr (pypy 6.0 for python 2.7)

### empty project

This is an `angr` analysis that does nothing but 
load an empty program into a project. The empty 
program  imports `stdlib.h` and `stdio.h`, and 
contains an empty `main` function.

This tells us the resources that `angr` needs, 
just to load up with pypy.

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.88      | 1.99      | 152096  |
    | 1.83      | 1.99      | 153160  |
    | 1.79      | 1.92      | 153132  |
    | 1.88      | 1.99      | 152344  |
    | 1.83      | 1.93      | 153336  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 1.84      | 1.96      | 152814  |
    -----------------------------------


### arith_register_jump (reg_jump)

Doesn't complete, just as with regular python.


### arith_reg_jump_short (short_jump)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 2.77      | 2.89      | 158580  |
    | 3.02      | 3.15      | 156412  |
    | 2.76      | 2.93      | 158452  |
    | 2.77      | 2.95      | 156692  |
    | 2.72      | 2.87      | 155924  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 2.81      | 2.96      | 157212  |
    -----------------------------------


### edges_torture (torture)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 3.84      | 4.01      | 164568  |
    | 4.00      | 4.20      | 164972  |
    | 3.97      | 3.99      | 165572  |
    | 3.98      | 4.16      | 164440  | 
    | 4.01      | 4.19      | 167924  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 3.96      | 4.11      | 165492  |
    -----------------------------------


### edges_torture_swapped (swapped)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 4.54      | 4.76      | 168368  |
    | 4.54      | 4.71      | 165436  |
    | 4.49      | 4.65      | 168880  |
    | 4.68      | 4.88      | 177624  | 
    | 4.65      | 4.84      | 176540  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 4.58      | 4.77      | 171370  |
    -----------------------------------


### jump_bomb (jump_bomb)

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 7.84      | 8.07      | 198736  |
    | 7.70      | 7.94      | 198548  |
    | 8.02      | 8.22      | 196948  |
    | 7.89      | 8.10      | 199200  | 
    | 7.90      | 8.12      | 197760  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 7.87      | 8.09      | 198238  |
    -----------------------------------


### simple_arithmetic_function_call (simple_call)

With PyPy, `angr` throws some runtime errors for
this analysis, but it completes anyway. 

Raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 6.17      | 6.32      | 198476  |
    | 6.34      | 6.46      | 197788  |
    | 6.11      | 6.28      | 198912  |
    | 6.17      | 6.34      | 196528  | 
    | 5.99      | 6.20      | 197856  |
    -----------------------------------

Averages of the raw data:

    -----------------------------------
    | User time | Wall time | RSS     |
    -----------------------------------
    | 6.16      | 6.32      | 198112  |
    -----------------------------------

