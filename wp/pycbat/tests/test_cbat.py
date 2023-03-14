from cbat import run_wp
from cbat.helpers import PropertyBuilder, MemView
import z3
import tempfile
import subprocess

rax = z3.BitVec("RAX", 64)
init_rax = z3.BitVec("init_RAX", 64)
init_rdi = z3.BitVec("init_RDI", 64)


def run_code(code, postcond):

    with tempfile.NamedTemporaryFile(suffix=".c") as fp:
        with tempfile.TemporaryDirectory() as mydir:
            fp.write(code.encode())
            fp.flush()
            fp.seek(0)
            print(fp.readlines())
            outfile = mydir + "/fact"
            print(subprocess.run(["gcc",  "-g",  "-c", "-O1",
                                  "-o",  outfile, fp.name], check=True))

            print(subprocess.run(["objdump", "-d", outfile], check=True))
            return run_wp(outfile, func="fact", postcond=postcond)


def test1():
    code = '''
  int fact(int x){
    return 3;
  }
  '''

    postcond = rax == 3

    assert run_code(code, postcond)[0] == z3.unsat


def test2():
    code = '''
  int fact(int x){
    return 3;
  }
  '''
    postcond = rax == 4

    assert run_code(code, postcond)[0] == z3.sat


def test3():
    code = '''
  int fact(int x){
    return x + 3;
  }
  '''
    postcond = z3.Extract(31, 0, rax) == z3.Extract(31, 0, init_rdi) + 3
    # postcond = rax == init_rdi + 3

    assert run_code(code, postcond)[0] == z3.unsat


def test4():
    print("running test4")
    pb = PropertyBuilder(binary="resources/test4.o",
                         headers="int foo(int x, char y);")
    x, y = pb.fun_args("foo")
    init_x, init_y = pb.init_fun_args("foo")
    retval = pb.ret_val("foo")
    # This is using bitvector semantic. Not C int semantics. Sigh. Since I'm pretending, this is confusing.
    postcond = retval == init_x + 3
    precond = None
    (res, model) = run_wp("resources/test4.o", func="foo",
                          precond=precond, postcond=postcond, docker_image=None)
    assert res == z3.unsat

    postcond = retval == init_x + 4
    (res, model) = run_wp("resources/test4.o", func="foo",
                          precond=precond, postcond=postcond, docker_image=None)
    assert res == z3.sat


# I dunno. Something weird is going on with pytest and IO.
test4()
test1()
test2()
test3()
