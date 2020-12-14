        global __assert_fail:function (__assert_fail.end - __assert_fail)
        global main:function (main.end - main)
fmt:    db `- %s\n`
__assert_fail:
    mov rax, 60
    mov rdi, 3
    syscall
    ret
.end:
main:
        mov     rdi, 0x61
        cmp     rdi, 0x67
        je      __assert_fail
        ret
.end:
