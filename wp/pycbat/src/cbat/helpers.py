import z3
import angr


class MemView():
    def __init__(self, mem: z3.ArrayRef, addr: z3.BitVecRef, typ: angr.sim_type.SimType):
        self.mem = mem
        self.addr = addr
        self.typ = typ

    def deref(self):
        addr = self.z3()
        return MemView(self.mem, addr, self.typ.pts_to)

    def z3(self):
        # check endian
        return z3.Concat([self.mem[self.addr + n] for n in range(self.typ.size // 8)])

    def __getitem__(self, field):
        addr = self.addr + self.typ.offsets[field]
        return MemView(self.mem, addr, self.typ.fields[field])

    def __repr__(self):
        return f"({repr(self.typ)}){repr(self.mem)}[{repr(self.addr)}]"


class PropertyBuilder():
    def __init__(self, binary=None, headers=None):
        if binary != None:
            self.load_binary(binary)
        if headers != None:
            self.load_headers(headers)

        def make_mem(name):
            return z3.Array(name, z3.BitVecSort(64), z3.BitVecSort(8))
        self.mem = make_mem("mem")
        self.init_mem = make_mem("init_mem")

    def load_binary(self, filename):
        self.proj = angr.Project(filename, load_debug_info=True)
        self.cc = self.proj.factory.cc()

    def load_headers(self, header_str):
        (defns, types) = angr.types.parse_file(header_str)
        angr.types.register_types(types)
        self.defns = defns

    def fun_args(self, func, prefix="", suffix=""):
        funsig = self.defns[func]
        funsig = funsig.with_arch(self.proj.arch)
        # stack args not supported yet
        assert len(funsig.args) <= len(self.cc.ARG_REGS)
        return [z3.Extract(arg.size - 1, 0, z3.BitVec(prefix + reg.upper() + suffix, 64)) for arg, reg in zip(funsig.args, self.cc.ARG_REGS)]

    def init_fun_args(self, func):
        return self.fun_args(func, prefix="init_")

    def ret_val(self, func):
        funsig = self.defns[func]
        funsig = funsig.with_arch(self.proj.arch)
        reg = self.cc.RETURN_VAL.reg_name
        return z3.Extract(funsig.returnty.size - 1, 0, z3.BitVec(reg.upper(), 64))
