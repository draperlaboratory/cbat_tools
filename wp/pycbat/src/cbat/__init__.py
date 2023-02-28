import subprocess
import z3


def run_wp(filename, filename2=None,  func="main", invariants=[], precond=None, postcond=None, docker_image="philzook58/cbat_min", **kwargs):
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

    if docker_image != None:
        flags = ["-it", "-v", f"{filename}:{filename}"]
        if filename2 != None:
            flags += ["-v", f"{filename2}:{filename2}"]
        cmd = ["docker", "run"] + flags + [docker_image] + cmd
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
