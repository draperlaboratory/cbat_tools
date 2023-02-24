

import subprocess
import z3
import docker

IMAGE = "philzook58/cbat_min"
client = docker.from_env()
print("Downloading CBAT Docker Image")
client.images.pull(IMAGE)
print("Download finished")

'''
# import angr  # , monkeyhex
class Reg(Z3BitVec):
class Mem(Z3Array):

class 
class PostCond():
    def __init__(self):
        self.precond
    @property
    def init(self):
    @property
    def mod(self):
    def orig(self):
    def high # C?
    def low 
    def sexpr():

    def mem():

class HighVar():
    def __init__(self, typ, lowloc):
        self.type = angr.type(typ)
    def 

class Correspondence # Bisim?

class LowVar():


class NameBuilder()
    def __init__():
        self.prefix = ""
        self.suffix = ""
    # This property stuff seems too clever for it's own good.
    @property
    def init
    def orig
    def mod

variable dictionary:
{
    init: {reg : z3.BitVec(capital(f"init_{reg}"), reg.size()) for reg in state}
    mod: {}
    orig: {}
    "C" : { cvar :  z3.BitVec()  for cvar in api } 
}

state1.high["foo"] == state2.high["foo"]
state1.high["foo"].field1.field2->field3

foo = state1.high["foo"]
state1.mem[]
Do lowering now or put it all in cbat?


class Z3View(Z3Expr):
    
    def __init__(self):
        mem
        addr
        typ = angr.type()
    def cast():
        return Concat(mem[addr], mem[addr+1], ...)
    def as_type():
    def field(self, name):
    def deref(self):
        


mem[foo + fieldy].as64 + 
    

class CBATModel():


'''


def run_wp(filename, filename2=None,  func="main", invariants=[], precond=None, postcond=None, use_docker=True, **kwargs):
    cmd = ["bap", "wp", "--no-cache",
           "--show", "precond-smtlib", "--func", func]
    if precond != None:
        cmd.append("--precond")
        cmd.append("(assert " + precond.sexpr() + ")")
    if postcond != None:
        cmd.append("--postcond")
        cmd.append("(assert " + postcond.sexpr() + ")")

    # forward kwargs. Typo unfriendly
    flags = ["check-invalid-derefs", "check-null-derefs"]  # and so on
    assert all(k in flags for k in kwargs.keys())
    cmd += [f"--{k}" for k,
            v in kwargs.items() if v == True and k in flags]

    cmd.append(filename)
    if filename2 != None:
        cmd.append(filename2)

    if use_docker:
        cmd = ["docker", "run", "-it",
               "-v", f"{filename}:{filename}", IMAGE] + cmd
        '''
        # Having a lot of trouble with the docker library here :(
        try:
            docker_res = client.containers.run("38c124f7f4f6", cmd, volumes={
                filename: {'bind': filename, 'mode': 'ro'}}, auto_remove=True, stderr=True)
        except docker.errors.ContainerError as e:
            print(e)
            print(e.stderr)
            raise e
        print(docker_res)
        stdout = docker_res
        '''
    res = subprocess.run(cmd, check=False, capture_output=True)
    print(res.args)
    print(res.stdout.decode())
    stdout = res.stdout.decode()
    smtlib = stdout.split("Z3 :")[1]
    s = z3.Solver()
    s.from_string(smtlib)
    print(s)
    res = s.check()
    if res == z3.unsat:
        return (z3.unsat, f"Property {postcond} proved")
    elif res == z3.sat:
        # raise?
        return (z3.sat, s.model())


"""

run () {
    bap wp main main.patched \
        --no-cache \
        --no-objdump \
        --ogre-orig=./vibes/loader.ogre \
        --ogre-mod=./main.patched.ogre \
        --func=main \
        --show=diagnostics \
        --postcond="(assert (= (bvadd R0_mod #x00000002) R0_orig))"
}
"""


"""
NAME
       bap-wp - wP is a comparative analysis tool

SYNOPSIS
       bap wp [OPTION]… [VAL]…

       WP is a comparative analysis tool. It can compare two binaries and
       check that they behave in similar ways. It can also be used to check a
       single binary for certain behaviors.

ARGUMENTS
       VAL Path(s) to one or two binaries to analyze. If two binaries are
           specified, WP will run a comparative analysis. If 0 or more than 2
           files are given, WP will exit with an error message.

OPTIONS
       --bildb-output=VAL
           When WP results in SAT, outputs a BILDB initialization script to
           the filename specified. This YAML file sets the registers and
           memory to the values found in the countermodel, allowing BILDB to
           follow the same execution trace. In the case WP returns UNSAT or
           UNKNOWN, no script will be outputted.

       --check-invalid-derefs
           This flag is only used in a comparative analysis. Checks that the
           modified binary has no additional paths that result in dereferences
           to invalid memory locations. That is, all memory dereferences are
           either on the stack or heap. The stack is defined as the memory
           region above the current stack pointer, and the heap is defined as
           the memory region 0x256 bytes below the lowest address of the
           stack.

       --check-null-derefs
           Checks for inputs that would result in dereferencing a null value
           during a memory read or write. In the case of a comparative
           analysis, checks that the modified binary has no additional paths
           with null dereferences in comparison with the original binary.

       --compare-func-calls
           This flag is only used in a comparative analysis. Checks that
           function calls do not occur in the modified binary if they have not
           occurred in the original binary.

       --compare-post-reg-values=VAL
           This flag is only used in a comparatve analysis. Compares the
           values stored in the specified registers at the end of the
           function's execution. For example, `RAX,RDI' compares the values of
           RAX and RDI at the end of execution. If unsure about which
           registers to compare, check the architecture's ABI. x86_64
           architectures place their output in RAX, and ARM architectures
           place their output in R0.

       --debug=VAL
           A list of various debugging statistics to display. Multiple
           statistics may be specified in a comma-separated list. For example:
           `--debug=z3-solver-stats,z3-verbose'. The options are:
           `z3-solver-stats': Information and statistics about Z3's solver. It
           includes information such as the maximum amount of memory used and
           the number of allocations. `z3-verbose': Z3's verbosity level. It
           outputs information such as the tactics the Z3 solver used.
           `constraint-stats': Statistics regarding the internal `Constr.t'
           data structure, including the number of goals, ITEs, clauses, and
           substitutions. `eval-constraint-stats': Statistics regarding the
           internal expression lists during evaluation of the `Constr.t' data
           type.

       --ext-solver-path=VAL
           Path of external smt solver to call. Boolector recommended.

       --fun-specs=VAL
           List of built-in function summaries to be used at a function call
           site in order of precedence. A target function will be mapped to a
           function spec if it fulfills the spec's requirements. All function
           specs set the target function as called and update the stack
           pointer. The default specs set are verifier-assume,
           varifier-nondet, empty, and chaos-caller-saved. Note that if a
           function is set to be inlined, it will not use any of the following
           function specs. Available built-in specs: `verifier-error': Used
           for calls to __VERIFIER_error and __assert_fail. Looks for inputs
           that would cause execution to reach these functions.
           `verifier-assume': Used for calls to __VERIFIER_assume. Adds an
           assumption to the precondition based on the argument to the
           function call. `verifier-nondet': Used for calls to
           nondeterministic functions such as __VERIFIER_nondet_*, calloc, and
           malloc. Chaoses the output to the function call representing an
           arbitrary pointer. `afl-maybe-log': Used for calls to
           __afl_maybe_log. Chaoses the registers RAX, RCX, and RDX.
           `arg-terms': Used when BAP's uplifter returns a nonempty list of
           input and output registers for the target function. Chaoses this
           list of output registers. `chaos-caller-saved': Used for the x86
           architecture. Chaoses the caller-saved registers. `rax-out': Chaos
           RAX if it can be found on the left-hand side of an assignment in
           the target function. `chaos-rax': Chaos RAX regardless if it has
           been used on the left-hand side of an assignment in the target
           function. `empty': Used for empty subroutines. Performs no actions.

       --func-name-map=VAL
           Maps the subroutine names from the original binary to their names
           in the modified binary based on the regex from the user. Usage:
           --func-name-map="<regex for original name>,<regex for modified
           name>". For example: --func-name-map="\(.*\),foo_\1" means that all
           subroutines in the original binary have foo_ prepended in the
           modified binary. Multiple patterns can be used to map function
           names and are delimited with ';'s (i.e.
           "<reg1_orig>,<reg1_mod>;<reg2_orig>,<reg2_mod>"). By default, WP
           assumes subroutines have the same names between the two binaries.

       --function=VAL, --func=VAL
           Determines which function to verify. WP verifies a single function,
           though calling it on the `main' function along with the `inline'
           option will analyze the whole program. If no function is specified
           or the function cannot be found in the binary/binaries, WP will
           exit with an error message.

       --gdb-output=VAL
           When WP results in SAT, outputs a gdb script to the filename
           specified. From within gdb, run `source filename.gdb' to set a
           breakpoint at the function given by `--func' and fill the
           appropriate registers with the values found in the countermodel. In
           the case WP returns UNSAT or UNKNOWN, no script will be outputted.

       --help[=FMT] (default=auto)
           Show this help in format FMT. The value FMT must be one of auto,
           pager, groff or plain. With auto, the format is pager or plain
           whenever the TERM env var is dumb or undefined.

       --init-mem
           This flag adds a number of hypotheses of the form mem[addr] == val,
           where the (addr, val) pairs come from the .rodata section of the
           binar(ies) under scrutiny.

       --inline=VAL
           Functions specified by the provided POSIX regular expression will
           be inlined. When functions are not inlined, heuristic function
           summaries are used at function call sites. For example, if you want
           to inline the functions `foo' and `bar', you can write
           `--inline=foo|bar'. To inline everything, use `--inline=.*' (not
           generally recommended).

       -L VAL, --plugin-path=VAL, --load-path=VAL
           Adds folder to the list of plugins search paths

       --logdir=VAL, --log-dir=VAL (absent BAP_LOG_DIR env)
           A folder for log files.

       --loop-invariant=VAL
           Usage: `(((address <addr>) (invariant <smtlib>)) (...))'. Assumes
           the subroutine contains unnested while loops with one entry point
           and one exit each. Checks the loop invariant written in smt-lib2
           format for the loop with its header at the given address. The
           address should be written in BAP's bitvector string format. Only
           supported for a single binary analysis.

       --mem-offset
           This flag is only used in a comparative analysis. Maps the symbols
           in the data and bss sections from their addresses in the original
           binary to their addresses in the modified binary. If this flag is
           not present, WP assumes that memory between both binaries start at
           the same offset.

       --no-chaos=VAL
           By default, nondeterministic functions and functions that allocate
           memory will use the Chaos function spec that freshens the output
           variable, "chaosing" its value as a result. Setting this flag will
           turn off this feature and treat the specified list as other
           functions that will use other function specs.

       --num-unroll=VAL
           Specifies the number of times to unroll each loop. WP will unroll
           each loop 5 times by default.

       --ogre=VAL
           Path of an ogre file, which will be used instead of the default BAP
           lifter. This is useful for stripped binaries, or to lift only a
           portion of a large binary.

       --ogre-mod=VAL
           Path of an ogre file, which will be used instead of the default BAP
           lifter for the modified binary in comparative analysis. This is
           useful for stripped binaries, or to lift only a portion of a large
           binary.

       --ogre-orig=VAL
           Path of an ogre file, which will be used instead of the default BAP
           lifter for the original binary in comparative analysis. This is
           useful for stripped binaries, or to lift only a portion of a large
           binary.

       --pointer-reg-list=VAL
           This flag specifies a comma delimited list of input registers to be
           treated as pointers at the start of program execution. This means
           that these registers are restricted in value to point to memory
           known to be initialized at the start of the function. For example,
           `RSI,RDI` would specify that `RSI` and `RDI`'s values should be
           restricted to initialized memory at the start of execution.

       --postcond=VAL
           Allows you to specify an assertion that WP will assume is true at
           the end of the function it is analyzing, using the smt-lib2 format.
           Similar to `--precond', one may create comparative postconditions
           on variables by appending `_orig' and `_mod' to variable names. If
           no postcondition is specified, a trivial postcondition of `true'
           will be used.

       --precond=VAL
           Allows you to specify an assertion that WP will assume is true at
           the beginning of the function it is analyzing. Assertions are
           specified in the smt-lib2 format. For comparative predicates, one
           may refer to variables in the original and modified programs by
           appending the suffix `_orig' and `_mod' to variable names in the
           smt-lib expression. For example, `--precond="(assert (= RDI_mod
           # x0000000000000003)) (assert (= RDI_orig #x0000000000000003))".' If
           no precondition is specified, a trivial precondition of `true' will
           be used.

       --recipe=VAL
           Load the specified recipe

       --rewrite-addresses
           This flag is only used in a comparative analysis. Rewrites the
           concrete addresses in the modified binary to the same address in
           the original binary if they point to the same symbol. This flag
           should not be used in conjunction with the `--mem-offset' flag.

       --show=VAL
           A list of details to print out from the analysis. Multiple options
           can be specified as a comma-separated list. For example:
           `--show=bir,refuted-goals'. The options are: `bir': The code of the
           binary/binaries in BAP Intermediate Representation.
           `refuted-goals': In the case WP results in SAT, a list of goals
           refuted in the model that contains their tagged names, their
           concrete values, and their Z3 representation. `paths': The
           execution path of the binary that results in a refuted goal. The
           path contains information about the jumps taken, their addresses,
           and the values of the registers at each jump. This option
           automatically prints out the refuted goals. `precond-smtlib': The
           precondition printed out in Z3's SMT-LIB2 format.
           `precond-internal': The precondition printed out in WP's internal
           format for the `Constr.t' type. `colorful': precond-internal can
           have color to highlight key words, making the output easier to
           read. Warning: Coloring will change the syntax, so don't use this
           flag if you wish to pass the printed output as an input elsewhere.
           `diagnostics': Prints out debugging information about runtime to
           stderr.

       --stack-base=VAL
           Sets the location of the stack frame for the function under
           analysis. By default, WP assumes the stack frame for the current
           function is between 0x40000000 and 0x3F800080.

       --stack-size=VAL
           Sets the size of the stack, which should be denoted in bytes. By
           default, the size of the stack is 0x800000 which is 8MB.

       --trip-asserts
           Looks for inputs to the subroutine that would cause an
           `__assert_fail' or `__VERIFIER_error' to be reached.

       --use-fun-input-regs
           At a function call site, uses all possible input registers as
           arguments to a function symbol generated for an output register. If
           this flag is not present, no registers will be used.

       --user-func-specs=VAL
           List of user-defined subroutine specifications. For each
           subroutine, it creates the weakest precondition given the name of
           the subroutine and its pre and post-conditions. Usage:
           --user-func-specs="<sub name>,<precondition>,<postcondition>". For
           example, --user-func-specs="foo,(assert (= RAX RDI)),(assert (= RAX
           init_RDI))" means "for subroutine named foo, specify that its
           precondition is RAX = RDI and its postcondition is RAX = init_RDI".
           Multiple subroutine specifications are delimited with ';'s, i.e.:
           --user-func-specs="foo,(assert (= RAX RDI)),(assert (= RAX
           init_RDI)); bar,(assert (= RAX RDI)),(assert (= RAX init_RDI))".

       --user-func-specs-mod=VAL
           List of user-defined subroutine specifications to be used only for
           the modified binary in comparative analysis. Usage: See
           --user-func-specs.

       --user-func-specs-orig=VAL
           List of user-defined subroutine specifications to be used only for
           the original binary in comparative analysis. Usage: See
           --user-func-specs.

       --version
           Show version information.
"""
