.global _start

.text

offset:
    ret

indirect_call:
    callq *%rdi
    mov (%rsp), %rax
    ret


main:
    ret

_start:
    call main
