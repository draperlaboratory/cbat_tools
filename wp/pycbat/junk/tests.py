from cbat import run_wp
import z3
import tempfile
import subprocess
code = '''
int fact(int x){
  int acc = 1;
  while(x > 0){
    acc *= x;
    x--;
  }
  return acc;
}
'''


code = '''
struct abcd {
    int x,
    int y
}
int fact(struct abcd* x){
  return x->y + 3;
}
'''

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


code = '''
int fact(int x){
  return 3;
}
'''

postcond = rax == 3

assert run_code(code, postcond)[0] == z3.unsat

code = '''
int fact(int x){
  return 3;
}
'''
postcond = rax == 4

assert run_code(code, postcond)[0] == z3.sat

code = '''
int fact(int x){
  return x + 3;
}
'''
postcond = z3.Extract(31, 0, rax) == z3.Extract(31, 0, init_rdi) + 3
# postcond = rax == init_rdi + 3

assert run_code(code, postcond)[0] == z3.unsat
