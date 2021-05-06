section .text
	global main

subroutine:	
	mov rdi, [rsi]

main:
	mov DWORD [rsi], 3
	call subroutine
	mov rax, rdi
	ret
