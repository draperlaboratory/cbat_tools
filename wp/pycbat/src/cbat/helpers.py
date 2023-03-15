import z3
import angr


class TypedView():
    def __init__(self, value: z3.BitVecRef, typ: angr.sim_type.SimType, le=True, mem=None):
        self.mem = mem
        self.value = value
        self.typ = typ
        self.le = True

    def deref(self):
        assert self.mem != None
        bytes = range(self.typ.size // 8)
        if self.le:
            bytes = reversed(bytes)
        value = z3.Concat([self.mem[self.value + n] for n in bytes])
        return TypedView(value, self.typ.pts_to, le=self.le, mem=self.mem)

    def __getitem__(self, field):
        start = self.typ.offsets[field]
        end = start + self.typ.fields[field].size
        value = z3.Extract(end-1, start, self.value)
        return TypedView(value, self.typ.fields[field], mem=self.mem, le=self.le)

    def __add__(self, b):
        if isinstance(b, int):
            return TypedView(self.value + b, self.typ, mem=self.mem, le=self.le)
        elif isinstance(b, TypedView):
            assert b.typ == self.typ and self.mem == b.mem and self.le == b.le
            return TypedView(self.value + b.value, self.typ, mem=self.mem, le=self.le)
        assert False, "Unexpected addition type"

    def __eq__(self, b):
        assert self.typ == b.typ
        return self.value == b.value

    def __repr__(self):
        return f"({repr(self.typ)}){repr(self.value)}"


def make_mem(name):
    return z3.Array(name, z3.BitVecSort(64), z3.BitVecSort(8))


class PropertyBuilder():
    def __init__(self, binary=None, headers=None):
        if binary != None:
            self.load_binary(binary)
        if headers != None:
            self.load_headers(headers)

        self.mem = make_mem("mem")
        self.init_mem = make_mem("init_mem")
        self.mem0 = make_mem("mem0")
        self.init_mem0 = make_mem("init_mem0")

    def load_binary(self, filename):
        self.proj = angr.Project(filename, load_debug_info=True)
        self.cc = self.proj.factory.cc()

    def load_headers(self, header_str):
        (defns, types) = angr.types.parse_file(header_str)
        angr.types.register_types(types)
        self.defns = defns

    def cast(self, value, typ, prefix="", suffix=""):
        mem = make_mem(prefix+"mem"+suffix)
        le = self.proj.arch.memory_endness == 'Iend_LE'
        value = z3.Extract(typ.size - 1, 0, value)
        return TypedView(value, typ, le=le, mem=mem)

    def fun_args(self, func, prefix="", suffix=""):
        funsig = self.defns[func]
        funsig = funsig.with_arch(self.proj.arch)
        # stack args not supported yet
        assert len(funsig.args) <= len(self.cc.ARG_REGS)
        return [self.cast(z3.BitVec(prefix + reg.upper() + suffix, 64), typ, prefix=prefix, suffix=suffix) for typ, reg in zip(funsig.args, self.cc.ARG_REGS)]

    def init_fun_args(self, func):
        return self.fun_args(func, prefix="init_")

    def ret_val(self, func):
        funsig = self.defns[func]
        funsig = funsig.with_arch(self.proj.arch)
        reg = self.cc.RETURN_VAL.reg_name
        return self.cast(z3.BitVec(reg.upper(), 64), funsig.returnty)
