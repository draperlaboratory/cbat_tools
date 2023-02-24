# CBAT Python Bindings

<https://github.com/draperlaboratory/cbat_tools>


Installation
```
python3 -m pip install -e .
```

Usage:

```python
import z3
import cbat

rax = z3.BitVec("RAX", 64)
postcond = rax == 4
# Check that rax is always 4 at end of function "fact" in binary file myfactorial.o
cbat.run_wp("./myfactorial.o", func="fact", postcond=postcond)
```

