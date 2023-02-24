import angr
import inspect
proj = angr.Project("foo.o")
print(proj.arch)
t = angr.types.parse_type('int')
t.arch = proj.arch
# print(inspect.getmembers(t))
print(dir(t))
print(t.base)
print(t.c_repr)
print(t.label)
print(t.signed)
t2 = t.with_arch(proj.arch)
print(t2.alignment)
# print(help(t2.extract))
