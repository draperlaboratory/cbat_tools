global __assert_fail:function (__assert_fail.end - __assert_fail)
global main:function (main.end - main)

fmt: db `- %s\n`

__assert_fail:
    mov     rax, 60
    mov     rdi, 3
    syscall
    ret
.end:

main:
    jmp     __assert_fail
  ret
.end:
