.global _start

.text

main:
    movq    %rdi, %rax
    inc     %rax
    ret

_start:
    call    main
    mov     $0x3c, %rax
    xor     %rdi,  %rdi
    syscall
