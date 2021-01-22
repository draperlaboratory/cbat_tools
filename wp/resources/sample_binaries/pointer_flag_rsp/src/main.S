.global _start

.text

main:
    mov    1(%rdi), %rsi

_start:
    call   main
