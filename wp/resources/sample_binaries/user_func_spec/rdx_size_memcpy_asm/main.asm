section .text
	global main

subroutine:
	mov rax, rdi
	jmp sub1

sub1:
	test rdx,rdx		;see if (n == 0)
	jne sub2		;if (n != 0) enter loop

sub2:
	mov ecx, [rsi]
	mov [rax], cl
	add rax, 1		;dest++
	add rsi, 1		;src++
	sub rdx, 1		;n--
	
main:
	mov r8, 3 
	mov QWORD [rsi], 3 
	call subroutine
	mov r8, [rdi]
	mov [rax], r8
	ret
