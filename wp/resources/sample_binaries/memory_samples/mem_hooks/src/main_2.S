.global _start

.text

main:
    mov     (val),       %rax
    nop
    ret

_start:
    call    main
    mov     $0x3c,       %rax
    xor     %rdi,        %rdi
    syscall


.data

foo:
    .int    2

val:
    .int    1
