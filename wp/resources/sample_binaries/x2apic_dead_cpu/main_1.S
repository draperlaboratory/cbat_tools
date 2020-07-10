.text

x2apic_dead_cpu:
  mov    0x0(,%rdi,8),%rdx
  mov    (%rdx),%rax
  test   %rax,%rax
  je finish
  movq $0x0,(%rax)

finish:
  xor    %eax,%eax
  ret
