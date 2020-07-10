.text

x2apic_dead_cpu:
  mov    0x0(,%rdi,8),%rdx
  mov    (%rdx),%rax
  movq $0x0,(%rax)
  xor    %eax,%eax
  retq
