; ;  Idea:
; ;  Tests that our code sees and uses g's pre and post-conditions.
; ---------------------------------------------------------------------------
;
; To compile this:
;
;     nasm -f elf64 -o main.o main.asm
;     gcc -o main main.o
;
; To run it:
;
;     ./main
;

; Expose the following functions (include size for ELF symbol table):

        global __assert_fail:function (__assert_fail.end - __assert_fail)
        global g:function (g.end - g)
        global main:function (main.end - main)

; ---------------------------------------------------------------------------
        SECTION .rodata
; ---------------------------------------------------------------------------

; A format string to print each command line argument.
fmt:    db `- %s\n`


; ---------------------------------------------------------------------------
        SECTION .text
; ---------------------------------------------------------------------------

; This function mimics the commented c above

__assert_fail:
    mov rax, 60
    mov rdi, 3
    syscall
    ret
.end:

main:
    mov     rax, 0x61
    mov     rdi, rax
    cmp     rdi, 0x67
    je      __assert_fail
    ret
.end:
