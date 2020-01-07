.global _start

.text

main:
    inc     %rdi
    movq    %rdi, %rax
    ret

_start:
    call    main
    mov     $0x3c, %rax
    xor     %rdi,  %rdi
    syscall
