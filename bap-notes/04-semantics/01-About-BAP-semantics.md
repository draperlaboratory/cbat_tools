# Semantics

The "semantics" of a program at a label is, roughly speaking, what the program "does" to the state of the machine when it executes. BAP represents this as the following type:

```
'a Theory.effect
``` 

In other words, the semantics of a program at a particulal label is the "effect" the program will produce in a machine's state.

Some examples:

* The semantics of assigning a variable is to set a value for an identifier in the machine's state.
* The semantics of calculating a sum and putting the result in a register involves assigning a value to a register (a variable), but it might also involve updating a zero flag (another variable), an overflow flag (yet another variable), and so on.
* The semantics of writing to memory is to put a value in the memory at a particular address. 
* The semantics of jumping to some other label in the program is to update the value of the instruction pointer to the targeted label.

To encode the semantics of programs, BAP provides what it calls a "core theory." A core theory is a very general kind of assembly language. It has variables, integers, floating point numbers, jumps, if-then-elses, and the like.

When you want to stipulate what a program does at a particular label, you write it down as a core theory program, and you put that core theory program in the label's "semantics" slot (`Theory.Semantics.slot`). That core theory program then represents what the program "does" at that particular label.


## Toy example

For instance, suppose we have a simple binary program, and we are looking at a particular label that moves the number 3 into a register R2 (in pseudo-assembly):

```
mov R2, 0x03
```

What is the semantics of the program at this label? The semantics is what it "does," and what it "does" is assign the integer `3` to the variable `R2`. 

To encode that, we create a core theory program that assigns 3 to r2, which looks something like this (in pseudo-core theory code):

```
(set (var R2) (int 0x03))
```

Then, we store this little core theory program in the "semantics" slot of this program label. 

This little core theory program then "represents" what the program "does" at that particular label. 

At any point in a later analysis, if we want to know what the program does at that particular label, we can just look in the label's "semantics" slot to see. 


## Another toy example

Suppose we have a binary program that is meant to run on a machine with 8-bit words, a zero flag, and an overflow flag. Suppose we are looking at a particular label that adds 255 and 1, and then stores the result in the register R2 (in pseudo assembly):

```
mov R2, 0xff + 0x01
```

What is the semantics of the program at this label?

The semantics of this program is what it "does" to the state of the machine when it executes, and that involves three things.

* `R2` (a variable) is set to the sum of `0xff` and `0x01`, which is `0x00` (because the machine has 8 bit words, so it cannot hold anything bigger than `0xff`).
* Since the result of adding `0xff` and `0x01` is zero, the zero flag `ZF` (another variable) is set to `0x01`.
* Third, since adding `0xff` and `0x01` is an overflow, the overflow flag `OF` (another variable) is set to `0x01`.

To encode this, we could create a core theory program that does all three of these things. It might look something like this (in pseudo-core theory code):

```
(
  (set (var R2) (add (int 0xff) (int 0x01)))
  (set (var ZF) (int 0x01))
  (set (var OF) (int 0x01)) 
)
```

We can then store this little core theory program in the "semantics" slot of this particular program label, so that at any later time, we can look up what the program at this particular label "does."

## Documentation

For more details, see the [documentation](https://binaryanalysisplatform.github.io/bap/api/master/bap-core-theory/Bap_core_theory/index.html).
