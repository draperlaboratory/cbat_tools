section .text
	global main

greg_memcpy:
	mov rdi, rsi

main:
	mov rsi, 2
	call greg_memcpy
	mov rax, rdi
	ret
