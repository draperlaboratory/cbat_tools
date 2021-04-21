section .text
	global main

greg_memcpy:
	mov rsi, rdi

main:
	call greg_memcpy
	mov rax, rdi
	ret
