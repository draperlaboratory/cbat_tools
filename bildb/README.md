# BILDB

This is a Primus-based BIL debugger. As it executes the program you give it,
it prints each BIL instruction to the screen, and pauses to let you debug.
At that point, you can view the value of registers, you can see what's stored
at some memory location, you can change the values of registers and memory,
and so on. You can step forwards and backwards one instruction at a time,
or you can set breakpoints, so you can skip ahead/backward to the next
breakpoint or basic block.


## A sample executable

There is a sample executable in the [resources/] folder. Build it from
the root of this repo:

    make -C resources

Clean it from the root of this repo:

    make exe.clean -C resources


## Install

To clean, build, and install `bildb` as a Primus component, from the root
of the repo:

    make

Once it's installed, see the help:

    bap --bildb-help

To uninstall and clean:

    make clean


## Usage

To run the program, the format is this:

    bap /path/to/exe --pass=run --bildb-debug

In essence, you start `bildb` just like any other Primus component, using
the `run` pass. By adding the `--bildb-debug` flag, you trigger the debugger.

When `bildb` starts up, it will print some information about the architecture,
and then it will stop at the first instruction. For example, if you start up
`bildb` on the sample executable:

    bap resources/main --pass=run --bildb-debug

You will see this:

```
BIL Debugger
Starting up...

Architecture
Type: x86_64
Address size: 64
Registers:
R10    R11    R12    R13    R14    R15    R8     R9     RAX    RBP    RBX    
RCX    RDI    RDX    RSI    RSP    YMM0   YMM1   YMM10  YMM11  YMM12  YMM13  
YMM14  YMM15  YMM2   YMM3   YMM4   YMM5   YMM6   YMM7   YMM8   YMM9   

Entering subroutine: [%000007c6] _start
Entering block %000000df
000000ea: RBP := 0
>>> (h for help) 
```

You are now prompted to enter a command for the debugger. To step to the next
instruction, type `s` (for "step") and hit `enter`. You will see the next
instruction, folowed by another prompt:

```
000000ed: AF := unknown[bits]:u1
>>> (h for help) 
```

You can repeat the last command you typed by hitting `enter`. So, to step
again, hit `enter`. That will take you to the next instruction:

```
000000f0: ZF := 1
>>> (h for help) 
```

To see more instructions, say the nearest 5 instructions before and after
the current one you're looking at, type `show 5`, and hit `enter`. You will
see something like this:

```
   %000000df
   000000ea: RBP := 0
   000000ed: AF := unknown[bits]:u1
-> 000000f0: ZF := 1
   000000f3: PF := 1
   000000f6: OF := 0
   000000f9: CF := 0
   000000fc: SF := 0
>>> (h for help) 
```

If you prefer to alway see the nearest, say, 5 instructions before and after,
type `always show 5` and hit `enter`. To return to seeing no extra instructions,
type `always show 0` and hit `enter`. 

To set a breakpoint, say at the TID `000000f9`, type `b %000000f9`, and hit
`enter`. It will tell you that you've set the breakpoint:

```
Breakpoint set at %000000f9
>>> (h for help) 
```

Now look at the nearest +/- 5 instructions again by typing `show 5`:

```
   %000000df
   000000ea: RBP := 0
   000000ed: AF := unknown[bits]:u1
-> 000000f0: ZF := 1
   000000f3: PF := 1
   000000f6: OF := 0
 b 000000f9: CF := 0
   000000fc: SF := 0
>>> (h for help) 
```

You can see the `b` next to TID `000000f9`, to indicate that there is a
breakpoint there.

To see all the breakpoints, type `breaks`, and hit `enter`. In this case, there is just one.

To remove a breakpoint, say the one we just set, type `clear %000000f9`
and hit `enter`. 

```
Breakpoint cleared at %000000f9
>>> (h for help) 
```

Let's set that breakpoint again. Type `b %000000f9`, and hit
`enter`, at which point it will tell you that you've set the breakpoint:

```
Breakpoint set at %000000f9
>>> (h for help) 
```

To skip to the next breakpoint (or the next basic block, whichever comes 
first), type `n` (for "next"), and hit enter. You will see that you have
moved to TID `000000f9`, which is where we set the breakpoint:

```
000000f9: CF := 0
>>> (h for help)
``` 

To move backwards one instruction, type `-s` and hit `enter`. You will see
that you have moved back one step, to TID `000000f6`:

```
000000f6: OF := 0
>>> (h for help) 
```

To move all the way back to the nearest breakpoint or basic block (whichever
comes first), type `-n` and hit `enter`. Since there are no other basic blocks
or break points in this program before we get back to the beginning, `bildb`
will stop back at the first instruction:

```
At program start
000000ea: RBP := 0
>>> (h for help)
```

To see the value of a register, type `p RAX` (`p` is short for "print"). 
You will see the value printed out:

```
RAX   : 0
>>> (h for help)
```

To set RAX to some particular value, for example `0xabc`, type
`set RAX=0xabc`, and hit `enter`. You will see that it has updated
RAX with the new value:

```
RAX   : 0xABC
>>> (h for help)
```

To see the byte stored at a memory address, say 0x3fffff1, type
`p 0x3ffffff1` and hit `enter`. You will see the value stored there:

```
0x3FFFFFF1: 0xD9 
>>> (h for help)
```

To see, say, the next 4 consecutive bytes stored in memory starting at 
0x3fffff1, type `p 0x3ffffff1 4` and hit `enter`. You will see each
byte at each address printed out:

```
0x3FFFFFF1: 0xD9  0x3FFFFFF2: 0x9E  0x3FFFFFF3: 0x7F  0x3FFFFFF4: 0x4C
>>> (h for help)
```

To store a byte at an address, e.g., to store 0x44 at 0x3ffffff1, type
`set 0x3ffffff1=0x44` and hit `enter`. You will see the new value:

```
0x3FFFFFF1: 0x44
>>> (h for help)
```

To see the full list of commands available to you, type `h` and hit `enter`. 
This will diplay the help menu.

To quit at any time, type `q` and hit `enter`.


## Initial state

If you want `bildb` to initialize certain variables and memory locations
before it starts running through the program, you can create an init file
with this format:

```
Variables:
  R8: 0x0000000
  R9: 0x7fffffff
  RAX: 0x00000abc
  RCX: 0x00000000
  RDI: 0x00000000
  RDX: 0x00000000
  RSI: 0x00000000
Locations:
  0x3ffffff1: 0x00000012
  0x3ffffff9: 0x000000ab
```

Save it as `init.yml`. Then start `bildb` with `--bildb-init=init.yml`,
like this:

    bap /path/to/exe --pass=run --bildb-debug --bildb-init=init.yml

When `bildb` starts up, it will print a message informing you of which
variables and memory locations it initialized:

```
IL Debugger
Starting up...

Architecture
Type: x86_64
Address size: 64
Registers:
R10    R11    R12    R13    R14    R15    R8     R9     RAX    RBP    RBX    
RCX    RDI    RDX    RSI    RSP    YMM0   YMM1   YMM10  YMM11  YMM12  YMM13  
YMM14  YMM15  YMM2   YMM3   YMM4   YMM5   YMM6   YMM7   YMM8   YMM9   

Initialized state
Variables:
RSI   : 0           RDX   : 0           RDI   : 0           RCX   : 0           
RAX   : 0xABC       R9    : 0x7FFFFFFF  R8    : 0           
Locations:
0x3FFFFFF9: 0xAB   0x3FFFFFF1: 0x12  

Entering subroutine: [%000007c6] _start
Entering block %000000df
000000ea: RBP := 0
>>> (h for help) 
```

You can see from the output that it set `RAX` to `0xABC`, and `R9` to `0x7FFFFFFF`, just as was specified in the init file. Also, the memory locations are initialized too, in accordance with what was specified in the init file. 
