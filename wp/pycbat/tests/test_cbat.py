from cbat import run_wp
from cbat.helpers import PropertyBuilder
import z3
import tempfile
import subprocess
import angr
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
    pb = PropertyBuilder(binary="resources/test4.o", func="foo",
                         headers="int foo(int x, char y);")
    x, y = pb.fun_args()
    init_x, init_y = pb.init_fun_args()
    retval = pb.ret_val()
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


def test5():
    header = '''
      typedef struct mystruct
      {
          int f1;
          char f2;
      } mystruct;

      int foo(mystruct *x, char y);
      '''
    pb = PropertyBuilder(binary="resources/test5.o",
                         func="foo", headers=header)
    x, y = pb.fun_args()
    init_x, init_y = pb.init_fun_args()
    retval = pb.ret_val()
    postcond = retval.value == init_x.deref()["f1"].value + 3
    (res, model) = run_wp("resources/test5.o", func="foo",
                          postcond=postcond, docker_image=None)
    # debugging
    #retval = z3.Extract(31, 0, z3.BitVec("RAX0", 64))
    #init_mem0 = pb.init_mem0
    #init_x0, init_y0 = pb.init_fun_args("foo", prefix="init_", suffix="0")
    # x_init = MemView(init_mem0, init_x0, angr.types.parse_type(
    #    "mystruct").with_arch(pb.proj.arch))
    #postcond = retval == x_init0["f1"].z3() + 3
    # print(postcond)
    # print(model)
    # print(model.eval(postcond))
    # print(model.eval(x_init["f1"].z3()))
    #print(model.eval(x_init["f1"].z3() + 3))
    assert res == z3.unsat


def test_compare():
    header = "int foo(int x);"
    pb = PropertyBuilder(binary="resources/test6_1.o",
                         binary2="resources/test6_2.o", func="foo", headers=header)
    retorig = pb.ret_val_orig()
    retmod = pb.ret_val_mod()
    pb.add_post(retmod.value == retorig.value + 1)
    (res, s) = pb.run_wp()
    assert res == z3.unsat


# I dunno. Something weird is going on with pytest and IO.
test_compare()
test5()
test4()
test1()
test2()
test3()
