import subprocess
import z3


def run_wp(filename, filename2=None,  func="main", invariants=[], debug=False, precond=None, postcond=None, docker_image=None, **kwargs):
    cmd = ["bap", "wp", "--no-cache",
           "--show", "precond-smtlib", "--func", func]
    if precond != None:
        cmd.append("--precond")
        cmd.append("(assert " + precond.sexpr() + ")")
    if postcond != None:
        cmd.append("--postcond")
        cmd.append("(assert " + postcond.sexpr() + ")")
    # TODO: Fill out invariants

    # forward kwargs. Typo unfriendly
    # TODO: fill out other allowed flags
    flags = ["check-invalid-derefs", "check-null-derefs"]
    assert all(k in flags for k in kwargs.keys()), kwargs
    cmd += [f"--{k}" for k,
            v in kwargs.items() if v == True and k in flags]

    cmd.append(filename)
    if filename2 != None:
        cmd.append(filename2)

    if docker_image != None:
        flags = ["-v", f"{filename}:{filename}"]
        if filename2 != None:
            flags += ["-v", f"{filename2}:{filename2}"]
        cmd = ["docker", "run"] + flags + [docker_image] + cmd
    res = subprocess.run(cmd, check=False, capture_output=True)
    if debug:
        print(res.stderr)
    smt = res.stdout.decode().split("Z3 :")
    if len(smt) != 2:
        print("SMT formula extraction failed", smt)
        print(res.stderr)
        assert False
    smtlib = smt[1]
    s = z3.Solver()
    s.from_string(smtlib)
    if debug:
        print(s)
    res = s.check()
    if res == z3.unsat:
        return (z3.unsat, s)
    elif res == z3.sat:
        # raise?
        return (z3.sat, s)
