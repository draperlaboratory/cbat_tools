.global _start

.text

main:
    mov     (val),       %rax
    ret

_start:
    call    main
    mov     $0x3c,       %rax
    xor     %rdi,        %rdi
    syscall


.data

val:
    .int    1
