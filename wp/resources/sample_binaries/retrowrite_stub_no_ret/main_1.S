.global _start

.text

main:
    nop
    ret

_start:
    call   main
    mov    $0x0, %rbx
    mov    $0x1, %rax
    int    $0x80
