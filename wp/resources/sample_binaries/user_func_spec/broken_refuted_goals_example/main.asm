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
	mov rsi, 0x42
	mov rdi, 0x67
	mov QWORD [rsi + 1], 3 
	call subroutine
	mov rax, [rdi + 1]
	ret

	;; 
