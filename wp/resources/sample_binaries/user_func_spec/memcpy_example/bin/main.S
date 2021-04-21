	.file	"main.c"
	.text
.Ltext0:
	.globl	greg_memcpy
	.type	greg_memcpy, @function
greg_memcpy:
.LFB41:
	.file 1 "src/main.c"
	.loc 1 9 0
	.cfi_startproc
.LVL0:
	movq	%rdi, %rax
.LVL1:
	.loc 1 11 0
	testq	%rdx, %rdx
	je	.L2
	addq	%rdi, %rdx
.LVL2:
	movq	%rdi, %rcx
.LVL3:
.L3:
	.loc 1 12 0
	movzbl	(%rsi), %r8d
	movb	%r8b, (%rcx)
	.loc 1 13 0
	addq	$1, %rcx
.LVL4:
	.loc 1 14 0
	addq	$1, %rsi
.LVL5:
	.loc 1 11 0
	cmpq	%rcx, %rdx
	jne	.L3
.LVL6:
.L2:
	.loc 1 18 0
	rep ret
	.cfi_endproc
.LFE41:
	.size	greg_memcpy, .-greg_memcpy
	.globl	main
	.type	main, @function
main:
.LFB42:
	.loc 1 21 0
	.cfi_startproc
.LVL7:
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	pushq	%rbx
	.cfi_def_cfa_offset 24
	.cfi_offset 3, -24
	subq	$8, %rsp
	.cfi_def_cfa_offset 32
	movq	%rsi, %rbp
	.loc 1 23 0
	movl	$3, %edi
.LVL8:
	call	malloc@PLT
.LVL9:
	movq	%rax, %rbx
.LVL10:
	.loc 1 24 0
	movq	0(%rbp), %rax
.LVL11:
	movb	$97, (%rax)
	.loc 1 26 0
	movl	$3, %edx
	movq	0(%rbp), %rsi
	movq	%rbx, %rdi
	call	greg_memcpy
.LVL12:
	.loc 1 32 0
	movsbl	(%rbx), %eax
	.loc 1 33 0
	addq	$8, %rsp
	.cfi_def_cfa_offset 24
	popq	%rbx
	.cfi_def_cfa_offset 16
.LVL13:
	popq	%rbp
	.cfi_def_cfa_offset 8
.LVL14:
	ret
	.cfi_endproc
.LFE42:
	.size	main, .-main
.Letext0:
	.file 2 "/usr/lib/gcc/x86_64-linux-gnu/7/include/stddef.h"
	.file 3 "/usr/include/x86_64-linux-gnu/bits/types.h"
	.file 4 "/usr/include/x86_64-linux-gnu/bits/libio.h"
	.file 5 "/usr/include/stdio.h"
	.file 6 "/usr/include/x86_64-linux-gnu/bits/sys_errlist.h"
	.file 7 "/usr/include/stdlib.h"
	.section	.debug_info,"",@progbits
.Ldebug_info0:
	.long	0x3f7
	.value	0x4
	.long	.Ldebug_abbrev0
	.byte	0x8
	.uleb128 0x1
	.long	.LASF61
	.byte	0xc
	.long	.LASF62
	.long	.LASF63
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.long	.Ldebug_line0
	.uleb128 0x2
	.long	.LASF8
	.byte	0x2
	.byte	0xd8
	.long	0x38
	.uleb128 0x3
	.byte	0x8
	.byte	0x7
	.long	.LASF0
	.uleb128 0x4
	.byte	0x4
	.byte	0x5
	.string	"int"
	.uleb128 0x3
	.byte	0x4
	.byte	0x7
	.long	.LASF1
	.uleb128 0x3
	.byte	0x8
	.byte	0x5
	.long	.LASF2
	.uleb128 0x3
	.byte	0x8
	.byte	0x5
	.long	.LASF3
	.uleb128 0x3
	.byte	0x1
	.byte	0x8
	.long	.LASF4
	.uleb128 0x3
	.byte	0x2
	.byte	0x7
	.long	.LASF5
	.uleb128 0x3
	.byte	0x1
	.byte	0x6
	.long	.LASF6
	.uleb128 0x3
	.byte	0x2
	.byte	0x5
	.long	.LASF7
	.uleb128 0x2
	.long	.LASF9
	.byte	0x3
	.byte	0x8c
	.long	0x4d
	.uleb128 0x2
	.long	.LASF10
	.byte	0x3
	.byte	0x8d
	.long	0x4d
	.uleb128 0x5
	.byte	0x8
	.uleb128 0x6
	.byte	0x8
	.long	0x95
	.uleb128 0x3
	.byte	0x1
	.byte	0x6
	.long	.LASF11
	.uleb128 0x7
	.long	0x95
	.uleb128 0x3
	.byte	0x8
	.byte	0x7
	.long	.LASF12
	.uleb128 0x8
	.long	.LASF42
	.byte	0xd8
	.byte	0x4
	.byte	0xf5
	.long	0x228
	.uleb128 0x9
	.long	.LASF13
	.byte	0x4
	.byte	0xf6
	.long	0x3f
	.byte	0
	.uleb128 0x9
	.long	.LASF14
	.byte	0x4
	.byte	0xfb
	.long	0x8f
	.byte	0x8
	.uleb128 0x9
	.long	.LASF15
	.byte	0x4
	.byte	0xfc
	.long	0x8f
	.byte	0x10
	.uleb128 0x9
	.long	.LASF16
	.byte	0x4
	.byte	0xfd
	.long	0x8f
	.byte	0x18
	.uleb128 0x9
	.long	.LASF17
	.byte	0x4
	.byte	0xfe
	.long	0x8f
	.byte	0x20
	.uleb128 0x9
	.long	.LASF18
	.byte	0x4
	.byte	0xff
	.long	0x8f
	.byte	0x28
	.uleb128 0xa
	.long	.LASF19
	.byte	0x4
	.value	0x100
	.long	0x8f
	.byte	0x30
	.uleb128 0xa
	.long	.LASF20
	.byte	0x4
	.value	0x101
	.long	0x8f
	.byte	0x38
	.uleb128 0xa
	.long	.LASF21
	.byte	0x4
	.value	0x102
	.long	0x8f
	.byte	0x40
	.uleb128 0xa
	.long	.LASF22
	.byte	0x4
	.value	0x104
	.long	0x8f
	.byte	0x48
	.uleb128 0xa
	.long	.LASF23
	.byte	0x4
	.value	0x105
	.long	0x8f
	.byte	0x50
	.uleb128 0xa
	.long	.LASF24
	.byte	0x4
	.value	0x106
	.long	0x8f
	.byte	0x58
	.uleb128 0xa
	.long	.LASF25
	.byte	0x4
	.value	0x108
	.long	0x260
	.byte	0x60
	.uleb128 0xa
	.long	.LASF26
	.byte	0x4
	.value	0x10a
	.long	0x266
	.byte	0x68
	.uleb128 0xa
	.long	.LASF27
	.byte	0x4
	.value	0x10c
	.long	0x3f
	.byte	0x70
	.uleb128 0xa
	.long	.LASF28
	.byte	0x4
	.value	0x110
	.long	0x3f
	.byte	0x74
	.uleb128 0xa
	.long	.LASF29
	.byte	0x4
	.value	0x112
	.long	0x77
	.byte	0x78
	.uleb128 0xa
	.long	.LASF30
	.byte	0x4
	.value	0x116
	.long	0x62
	.byte	0x80
	.uleb128 0xa
	.long	.LASF31
	.byte	0x4
	.value	0x117
	.long	0x69
	.byte	0x82
	.uleb128 0xa
	.long	.LASF32
	.byte	0x4
	.value	0x118
	.long	0x26c
	.byte	0x83
	.uleb128 0xa
	.long	.LASF33
	.byte	0x4
	.value	0x11c
	.long	0x27c
	.byte	0x88
	.uleb128 0xa
	.long	.LASF34
	.byte	0x4
	.value	0x125
	.long	0x82
	.byte	0x90
	.uleb128 0xa
	.long	.LASF35
	.byte	0x4
	.value	0x12d
	.long	0x8d
	.byte	0x98
	.uleb128 0xa
	.long	.LASF36
	.byte	0x4
	.value	0x12e
	.long	0x8d
	.byte	0xa0
	.uleb128 0xa
	.long	.LASF37
	.byte	0x4
	.value	0x12f
	.long	0x8d
	.byte	0xa8
	.uleb128 0xa
	.long	.LASF38
	.byte	0x4
	.value	0x130
	.long	0x8d
	.byte	0xb0
	.uleb128 0xa
	.long	.LASF39
	.byte	0x4
	.value	0x132
	.long	0x2d
	.byte	0xb8
	.uleb128 0xa
	.long	.LASF40
	.byte	0x4
	.value	0x133
	.long	0x3f
	.byte	0xc0
	.uleb128 0xa
	.long	.LASF41
	.byte	0x4
	.value	0x135
	.long	0x282
	.byte	0xc4
	.byte	0
	.uleb128 0xb
	.long	.LASF64
	.byte	0x4
	.byte	0x9a
	.uleb128 0x8
	.long	.LASF43
	.byte	0x18
	.byte	0x4
	.byte	0xa0
	.long	0x260
	.uleb128 0x9
	.long	.LASF44
	.byte	0x4
	.byte	0xa1
	.long	0x260
	.byte	0
	.uleb128 0x9
	.long	.LASF45
	.byte	0x4
	.byte	0xa2
	.long	0x266
	.byte	0x8
	.uleb128 0x9
	.long	.LASF46
	.byte	0x4
	.byte	0xa6
	.long	0x3f
	.byte	0x10
	.byte	0
	.uleb128 0x6
	.byte	0x8
	.long	0x22f
	.uleb128 0x6
	.byte	0x8
	.long	0xa8
	.uleb128 0xc
	.long	0x95
	.long	0x27c
	.uleb128 0xd
	.long	0x38
	.byte	0
	.byte	0
	.uleb128 0x6
	.byte	0x8
	.long	0x228
	.uleb128 0xc
	.long	0x95
	.long	0x292
	.uleb128 0xd
	.long	0x38
	.byte	0x13
	.byte	0
	.uleb128 0xe
	.long	.LASF65
	.uleb128 0xf
	.long	.LASF47
	.byte	0x4
	.value	0x13f
	.long	0x292
	.uleb128 0xf
	.long	.LASF48
	.byte	0x4
	.value	0x140
	.long	0x292
	.uleb128 0xf
	.long	.LASF49
	.byte	0x4
	.value	0x141
	.long	0x292
	.uleb128 0x6
	.byte	0x8
	.long	0x9c
	.uleb128 0x7
	.long	0x2bb
	.uleb128 0x10
	.long	.LASF50
	.byte	0x5
	.byte	0x87
	.long	0x266
	.uleb128 0x10
	.long	.LASF51
	.byte	0x5
	.byte	0x88
	.long	0x266
	.uleb128 0x10
	.long	.LASF52
	.byte	0x5
	.byte	0x89
	.long	0x266
	.uleb128 0x10
	.long	.LASF53
	.byte	0x6
	.byte	0x1a
	.long	0x3f
	.uleb128 0xc
	.long	0x2c1
	.long	0x2fd
	.uleb128 0x11
	.byte	0
	.uleb128 0x7
	.long	0x2f2
	.uleb128 0x10
	.long	.LASF54
	.byte	0x6
	.byte	0x1b
	.long	0x2fd
	.uleb128 0x12
	.long	.LASF57
	.byte	0x1
	.byte	0x15
	.long	0x3f
	.quad	.LFB42
	.quad	.LFE42-.LFB42
	.uleb128 0x1
	.byte	0x9c
	.long	0x38c
	.uleb128 0x13
	.long	.LASF55
	.byte	0x1
	.byte	0x15
	.long	0x3f
	.long	.LLST4
	.uleb128 0x13
	.long	.LASF56
	.byte	0x1
	.byte	0x15
	.long	0x38c
	.long	.LLST5
	.uleb128 0x14
	.long	.LASF60
	.byte	0x1
	.byte	0x17
	.long	0x8f
	.long	.LLST6
	.uleb128 0x15
	.quad	.LVL9
	.long	0x3ee
	.long	0x372
	.uleb128 0x16
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x1
	.byte	0x33
	.byte	0
	.uleb128 0x17
	.quad	.LVL12
	.long	0x392
	.uleb128 0x16
	.uleb128 0x1
	.byte	0x55
	.uleb128 0x2
	.byte	0x73
	.sleb128 0
	.uleb128 0x16
	.uleb128 0x1
	.byte	0x51
	.uleb128 0x1
	.byte	0x33
	.byte	0
	.byte	0
	.uleb128 0x6
	.byte	0x8
	.long	0x8f
	.uleb128 0x12
	.long	.LASF58
	.byte	0x1
	.byte	0x9
	.long	0x8f
	.quad	.LFB41
	.quad	.LFE41-.LFB41
	.uleb128 0x1
	.byte	0x9c
	.long	0x3ee
	.uleb128 0x13
	.long	.LASF59
	.byte	0x1
	.byte	0x9
	.long	0x8f
	.long	.LLST0
	.uleb128 0x18
	.string	"src"
	.byte	0x1
	.byte	0x9
	.long	0x2bb
	.long	.LLST1
	.uleb128 0x18
	.string	"n"
	.byte	0x1
	.byte	0x9
	.long	0x2d
	.long	.LLST2
	.uleb128 0x19
	.string	"out"
	.byte	0x1
	.byte	0xa
	.long	0x8f
	.long	.LLST3
	.byte	0
	.uleb128 0x1a
	.long	.LASF66
	.long	.LASF66
	.byte	0x7
	.value	0x21b
	.byte	0
	.section	.debug_abbrev,"",@progbits
.Ldebug_abbrev0:
	.uleb128 0x1
	.uleb128 0x11
	.byte	0x1
	.uleb128 0x25
	.uleb128 0xe
	.uleb128 0x13
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x1b
	.uleb128 0xe
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x10
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x2
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x3
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0xe
	.byte	0
	.byte	0
	.uleb128 0x4
	.uleb128 0x24
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3e
	.uleb128 0xb
	.uleb128 0x3
	.uleb128 0x8
	.byte	0
	.byte	0
	.uleb128 0x5
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0x6
	.uleb128 0xf
	.byte	0
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x7
	.uleb128 0x26
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x8
	.uleb128 0x13
	.byte	0x1
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0xb
	.uleb128 0xb
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x9
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xa
	.uleb128 0xd
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x38
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xb
	.uleb128 0x16
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xc
	.uleb128 0x1
	.byte	0x1
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0xd
	.uleb128 0x21
	.byte	0
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2f
	.uleb128 0xb
	.byte	0
	.byte	0
	.uleb128 0xe
	.uleb128 0x13
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0xf
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0x5
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x10
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.byte	0
	.byte	0
	.uleb128 0x11
	.uleb128 0x21
	.byte	0
	.byte	0
	.byte	0
	.uleb128 0x12
	.uleb128 0x2e
	.byte	0x1
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x27
	.uleb128 0x19
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x12
	.uleb128 0x7
	.uleb128 0x40
	.uleb128 0x18
	.uleb128 0x2117
	.uleb128 0x19
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x13
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x14
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x15
	.uleb128 0x4109
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x31
	.uleb128 0x13
	.uleb128 0x1
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x16
	.uleb128 0x410a
	.byte	0
	.uleb128 0x2
	.uleb128 0x18
	.uleb128 0x2111
	.uleb128 0x18
	.byte	0
	.byte	0
	.uleb128 0x17
	.uleb128 0x4109
	.byte	0x1
	.uleb128 0x11
	.uleb128 0x1
	.uleb128 0x31
	.uleb128 0x13
	.byte	0
	.byte	0
	.uleb128 0x18
	.uleb128 0x5
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x19
	.uleb128 0x34
	.byte	0
	.uleb128 0x3
	.uleb128 0x8
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0xb
	.uleb128 0x49
	.uleb128 0x13
	.uleb128 0x2
	.uleb128 0x17
	.byte	0
	.byte	0
	.uleb128 0x1a
	.uleb128 0x2e
	.byte	0
	.uleb128 0x3f
	.uleb128 0x19
	.uleb128 0x3c
	.uleb128 0x19
	.uleb128 0x6e
	.uleb128 0xe
	.uleb128 0x3
	.uleb128 0xe
	.uleb128 0x3a
	.uleb128 0xb
	.uleb128 0x3b
	.uleb128 0x5
	.byte	0
	.byte	0
	.byte	0
	.section	.debug_loc,"",@progbits
.Ldebug_loc0:
.LLST4:
	.quad	.LVL7-.Ltext0
	.quad	.LVL8-.Ltext0
	.value	0x1
	.byte	0x55
	.quad	.LVL8-.Ltext0
	.quad	.LFE42-.Ltext0
	.value	0x4
	.byte	0xf3
	.uleb128 0x1
	.byte	0x55
	.byte	0x9f
	.quad	0
	.quad	0
.LLST5:
	.quad	.LVL7-.Ltext0
	.quad	.LVL9-1-.Ltext0
	.value	0x1
	.byte	0x54
	.quad	.LVL9-1-.Ltext0
	.quad	.LVL14-.Ltext0
	.value	0x1
	.byte	0x56
	.quad	.LVL14-.Ltext0
	.quad	.LFE42-.Ltext0
	.value	0x4
	.byte	0xf3
	.uleb128 0x1
	.byte	0x54
	.byte	0x9f
	.quad	0
	.quad	0
.LLST6:
	.quad	.LVL10-.Ltext0
	.quad	.LVL11-.Ltext0
	.value	0x1
	.byte	0x50
	.quad	.LVL11-.Ltext0
	.quad	.LVL13-.Ltext0
	.value	0x1
	.byte	0x53
	.quad	0
	.quad	0
.LLST0:
	.quad	.LVL0-.Ltext0
	.quad	.LVL3-.Ltext0
	.value	0x1
	.byte	0x55
	.quad	.LVL3-.Ltext0
	.quad	.LVL6-.Ltext0
	.value	0x1
	.byte	0x52
	.quad	0
	.quad	0
.LLST1:
	.quad	.LVL0-.Ltext0
	.quad	.LVL5-.Ltext0
	.value	0x1
	.byte	0x54
	.quad	.LVL5-.Ltext0
	.quad	.LFE41-.Ltext0
	.value	0x1
	.byte	0x54
	.quad	0
	.quad	0
.LLST2:
	.quad	.LVL0-.Ltext0
	.quad	.LVL2-.Ltext0
	.value	0x1
	.byte	0x51
	.quad	.LVL2-.Ltext0
	.quad	.LVL6-.Ltext0
	.value	0x4
	.byte	0xf3
	.uleb128 0x1
	.byte	0x51
	.byte	0x9f
	.quad	0
	.quad	0
.LLST3:
	.quad	.LVL1-.Ltext0
	.quad	.LVL3-.Ltext0
	.value	0x1
	.byte	0x55
	.quad	.LVL3-.Ltext0
	.quad	.LFE41-.Ltext0
	.value	0x1
	.byte	0x50
	.quad	0
	.quad	0
	.section	.debug_aranges,"",@progbits
	.long	0x2c
	.value	0x2
	.long	.Ldebug_info0
	.byte	0x8
	.byte	0
	.value	0
	.value	0
	.quad	.Ltext0
	.quad	.Letext0-.Ltext0
	.quad	0
	.quad	0
	.section	.debug_line,"",@progbits
.Ldebug_line0:
	.section	.debug_str,"MS",@progbits,1
.LASF9:
	.string	"__off_t"
.LASF14:
	.string	"_IO_read_ptr"
.LASF66:
	.string	"malloc"
.LASF26:
	.string	"_chain"
.LASF62:
	.string	"src/main.c"
.LASF32:
	.string	"_shortbuf"
.LASF49:
	.string	"_IO_2_1_stderr_"
.LASF20:
	.string	"_IO_buf_base"
.LASF12:
	.string	"long long unsigned int"
.LASF3:
	.string	"long long int"
.LASF6:
	.string	"signed char"
.LASF27:
	.string	"_fileno"
.LASF15:
	.string	"_IO_read_end"
.LASF2:
	.string	"long int"
.LASF58:
	.string	"greg_memcpy"
.LASF13:
	.string	"_flags"
.LASF21:
	.string	"_IO_buf_end"
.LASF30:
	.string	"_cur_column"
.LASF29:
	.string	"_old_offset"
.LASF34:
	.string	"_offset"
.LASF8:
	.string	"size_t"
.LASF63:
	.string	"/home/glt0413/cbat_tools/wp/resources/sample_binaries/user_func_spec/memcpy_example"
.LASF43:
	.string	"_IO_marker"
.LASF50:
	.string	"stdin"
.LASF1:
	.string	"unsigned int"
.LASF0:
	.string	"long unsigned int"
.LASF65:
	.string	"_IO_FILE_plus"
.LASF18:
	.string	"_IO_write_ptr"
.LASF53:
	.string	"sys_nerr"
.LASF45:
	.string	"_sbuf"
.LASF5:
	.string	"short unsigned int"
.LASF22:
	.string	"_IO_save_base"
.LASF33:
	.string	"_lock"
.LASF28:
	.string	"_flags2"
.LASF40:
	.string	"_mode"
.LASF51:
	.string	"stdout"
.LASF47:
	.string	"_IO_2_1_stdin_"
.LASF60:
	.string	"output"
.LASF19:
	.string	"_IO_write_end"
.LASF64:
	.string	"_IO_lock_t"
.LASF42:
	.string	"_IO_FILE"
.LASF59:
	.string	"dest"
.LASF46:
	.string	"_pos"
.LASF54:
	.string	"sys_errlist"
.LASF25:
	.string	"_markers"
.LASF4:
	.string	"unsigned char"
.LASF7:
	.string	"short int"
.LASF31:
	.string	"_vtable_offset"
.LASF48:
	.string	"_IO_2_1_stdout_"
.LASF11:
	.string	"char"
.LASF61:
	.string	"GNU C11 7.5.0 -mtune=generic -march=x86-64 -g -O1 -fno-stack-protector"
.LASF44:
	.string	"_next"
.LASF10:
	.string	"__off64_t"
.LASF16:
	.string	"_IO_read_base"
.LASF24:
	.string	"_IO_save_end"
.LASF35:
	.string	"__pad1"
.LASF36:
	.string	"__pad2"
.LASF37:
	.string	"__pad3"
.LASF38:
	.string	"__pad4"
.LASF39:
	.string	"__pad5"
.LASF41:
	.string	"_unused2"
.LASF52:
	.string	"stderr"
.LASF56:
	.string	"argv"
.LASF23:
	.string	"_IO_backup_base"
.LASF55:
	.string	"argc"
.LASF57:
	.string	"main"
.LASF17:
	.string	"_IO_write_base"
	.ident	"GCC: (Ubuntu 7.5.0-3ubuntu1~18.04) 7.5.0"
	.section	.note.GNU-stack,"",@progbits
