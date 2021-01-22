.global _start

.text

__afl_maybe_log:
    nop
    ret

main:
    nop
    lea    -0x98(%rsp), %rsp
    mov    %rdx, (%rsp)
    mov    %rcx, 0x8(%rsp)
    mov    %rax, 0x10(%rsp)
    mov    $0x8c8a, %rcx
    call   __afl_maybe_log
    mov    0x10(%rsp), %rax
    mov    0x8(%rsp), %rcx
    mov    (%rsp), %rdx
    lea    0x98(%rsp), %rsp
    nop
    ret

_start:
    call   main
    mov    $0x0, %rbx
    mov    $0x1, %rax
    int    $0x80
