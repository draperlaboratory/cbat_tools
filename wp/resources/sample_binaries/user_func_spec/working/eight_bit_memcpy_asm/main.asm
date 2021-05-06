section .text
	global main

subroutine:
	mov r8, [rsi]
	mov [rdi], r8

main:
	mov DWORD [rsi], 3
	call subroutine 
	mov rax, [rdi]
	ret
