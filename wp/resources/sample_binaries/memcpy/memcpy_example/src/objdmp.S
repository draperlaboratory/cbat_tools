
main:     file format elf64-littleaarch64


Disassembly of section .init:

0000000000400220 <_init>:
  400220:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  400224:	910003fd 	mov	x29, sp
  400228:	94000037 	bl	400304 <call_weak_fn>
  40022c:	a8c17bfd 	ldp	x29, x30, [sp], #16
  400230:	d65f03c0 	ret

Disassembly of section .plt:

0000000000400240 <.plt>:
  400240:	d00003f0 	adrp	x16, 47e000 <_GLOBAL_OFFSET_TABLE_+0xc0>
  400244:	f9400211 	ldr	x17, [x16]
  400248:	91000210 	add	x16, x16, #0x0
  40024c:	d61f0220 	br	x17
  400250:	d00003f0 	adrp	x16, 47e000 <_GLOBAL_OFFSET_TABLE_+0xc0>
  400254:	f9400611 	ldr	x17, [x16, #8]
  400258:	91002210 	add	x16, x16, #0x8
  40025c:	d61f0220 	br	x17
  400260:	d00003f0 	adrp	x16, 47e000 <_GLOBAL_OFFSET_TABLE_+0xc0>
  400264:	f9400a11 	ldr	x17, [x16, #16]
  400268:	91004210 	add	x16, x16, #0x10
  40026c:	d61f0220 	br	x17

Disassembly of section .text:

0000000000400280 <backtrace_and_maps.constprop.0>:
  400280:	d65f03c0 	ret

0000000000400284 <oom>:
  400284:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  400288:	b0000301 	adrp	x1, 461000 <msg.11981+0xc0>
  40028c:	910e0021 	add	x1, x1, #0x380
  400290:	52800040 	mov	w0, #0x2                   	// #2
  400294:	910003fd 	mov	x29, sp
  400298:	9400feea 	bl	43fe40 <_dl_dprintf>
  40029c:	52800fe0 	mov	w0, #0x7f                  	// #127
  4002a0:	94005bd2 	bl	4171e8 <_exit>
  4002a4:	00000000 	.inst	0x00000000 ; undefined

00000000004002a8 <fini>:
  4002a8:	90000400 	adrp	x0, 480000 <initial+0x40>
  4002ac:	f9435c00 	ldr	x0, [x0, #1720]
  4002b0:	14011114 	b	444700 <check_free.isra.0>

00000000004002b4 <_start>:
  4002b4:	d280001d 	mov	x29, #0x0                   	// #0
  4002b8:	d280001e 	mov	x30, #0x0                   	// #0
  4002bc:	aa0003e5 	mov	x5, x0
  4002c0:	f94003e1 	ldr	x1, [sp]
  4002c4:	910023e2 	add	x2, sp, #0x8
  4002c8:	910003e6 	mov	x6, sp
  4002cc:	d2e00000 	movz	x0, #0x0, lsl #48
  4002d0:	f2c00000 	movk	x0, #0x0, lsl #32
  4002d4:	f2a00800 	movk	x0, #0x40, lsl #16
  4002d8:	f2807f80 	movk	x0, #0x3fc
  4002dc:	d2e00003 	movz	x3, #0x0, lsl #48
  4002e0:	f2c00003 	movk	x3, #0x0, lsl #32
  4002e4:	f2a00803 	movk	x3, #0x40, lsl #16
  4002e8:	f2819103 	movk	x3, #0xc88
  4002ec:	d2e00004 	movz	x4, #0x0, lsl #48
  4002f0:	f2c00004 	movk	x4, #0x0, lsl #32
  4002f4:	f2a00804 	movk	x4, #0x40, lsl #16
  4002f8:	f281a904 	movk	x4, #0xd48
  4002fc:	940000b7 	bl	4005d8 <__libc_start_main>
  400300:	9400145c 	bl	405470 <abort>

0000000000400304 <call_weak_fn>:
  400304:	b00003e0 	adrp	x0, 47d000 <__FRAME_END__+0xfd54>
  400308:	f947f000 	ldr	x0, [x0, #4064]
  40030c:	b4000040 	cbz	x0, 400314 <call_weak_fn+0x10>
  400310:	d503201f 	nop
  400314:	d65f03c0 	ret

0000000000400318 <deregister_tm_clones>:
  400318:	f00003e0 	adrp	x0, 47f000 <__progname_full>
  40031c:	91286000 	add	x0, x0, #0xa18
  400320:	f00003e1 	adrp	x1, 47f000 <__progname_full>
  400324:	91286021 	add	x1, x1, #0xa18
  400328:	eb00003f 	cmp	x1, x0
  40032c:	540000a0 	b.eq	400340 <deregister_tm_clones+0x28>  // b.none
  400330:	d0000261 	adrp	x1, 44e000 <__gcc_personality_v0+0x1b0>
  400334:	f9479c21 	ldr	x1, [x1, #3896]
  400338:	b4000041 	cbz	x1, 400340 <deregister_tm_clones+0x28>
  40033c:	d61f0020 	br	x1
  400340:	d65f03c0 	ret
  400344:	d503201f 	nop

0000000000400348 <register_tm_clones>:
  400348:	f00003e0 	adrp	x0, 47f000 <__progname_full>
  40034c:	91286000 	add	x0, x0, #0xa18
  400350:	f00003e1 	adrp	x1, 47f000 <__progname_full>
  400354:	91286021 	add	x1, x1, #0xa18
  400358:	cb000021 	sub	x1, x1, x0
  40035c:	9343fc21 	asr	x1, x1, #3
  400360:	8b41fc21 	add	x1, x1, x1, lsr #63
  400364:	9341fc21 	asr	x1, x1, #1
  400368:	b40000a1 	cbz	x1, 40037c <register_tm_clones+0x34>
  40036c:	d0000262 	adrp	x2, 44e000 <__gcc_personality_v0+0x1b0>
  400370:	f947a042 	ldr	x2, [x2, #3904]
  400374:	b4000042 	cbz	x2, 40037c <register_tm_clones+0x34>
  400378:	d61f0040 	br	x2
  40037c:	d65f03c0 	ret

0000000000400380 <__do_global_dtors_aux>:
  400380:	a9be7bfd 	stp	x29, x30, [sp, #-32]!
  400384:	910003fd 	mov	x29, sp
  400388:	f9000bf3 	str	x19, [sp, #16]
  40038c:	f00003f3 	adrp	x19, 47f000 <__progname_full>
  400390:	39686260 	ldrb	w0, [x19, #2584]
  400394:	35000140 	cbnz	w0, 4003bc <__do_global_dtors_aux+0x3c>
  400398:	97ffffe0 	bl	400318 <deregister_tm_clones>
  40039c:	d0000260 	adrp	x0, 44e000 <__gcc_personality_v0+0x1b0>
  4003a0:	f947a400 	ldr	x0, [x0, #3912]
  4003a4:	b4000080 	cbz	x0, 4003b4 <__do_global_dtors_aux+0x34>
  4003a8:	90000340 	adrp	x0, 468000 <__PRETTY_FUNCTION__.12074+0xa0>
  4003ac:	913d8000 	add	x0, x0, #0xf60
  4003b0:	940135a8 	bl	44da50 <__deregister_frame_info>
  4003b4:	52800020 	mov	w0, #0x1                   	// #1
  4003b8:	39286260 	strb	w0, [x19, #2584]
  4003bc:	f9400bf3 	ldr	x19, [sp, #16]
  4003c0:	a8c27bfd 	ldp	x29, x30, [sp], #32
  4003c4:	d65f03c0 	ret

00000000004003c8 <frame_dummy>:
  4003c8:	d0000260 	adrp	x0, 44e000 <__gcc_personality_v0+0x1b0>
  4003cc:	f947a800 	ldr	x0, [x0, #3920]
  4003d0:	b4000140 	cbz	x0, 4003f8 <frame_dummy+0x30>
  4003d4:	a9bf7bfd 	stp	x29, x30, [sp, #-16]!
  4003d8:	f00003e1 	adrp	x1, 47f000 <__progname_full>
  4003dc:	90000340 	adrp	x0, 468000 <__PRETTY_FUNCTION__.12074+0xa0>
  4003e0:	91288021 	add	x1, x1, #0xa20
  4003e4:	910003fd 	mov	x29, sp
  4003e8:	913d8000 	add	x0, x0, #0xf60
  4003ec:	940134eb 	bl	44d798 <__register_frame_info>
  4003f0:	a8c17bfd 	ldp	x29, x30, [sp], #16
  4003f4:	17ffffd5 	b	400348 <register_tm_clones>
  4003f8:	17ffffd4 	b	400348 <register_tm_clones>

00000000004003fc <main>:
  4003fc:	a9b77bfd 	stp	x29, x30, [sp, #-144]!
  400400:	910003fd 	mov	x29, sp
  400404:	b9001fa0 	str	w0, [x29, #28]
  400408:	f9000ba1 	str	x1, [x29, #16]
  40040c:	b00003e0 	adrp	x0, 47d000 <__FRAME_END__+0xfd54>
  400410:	f947a800 	ldr	x0, [x0, #3920]
  400414:	f9400001 	ldr	x1, [x0]
  400418:	f90047a1 	str	x1, [x29, #136]
  40041c:	d2800001 	mov	x1, #0x0                   	// #0
  400420:	794053a0 	ldrh	w0, [x29, #40]
  400424:	52800841 	mov	w1, #0x42                  	// #66
  400428:	33002420 	bfxil	w0, w1, #0, #10
  40042c:	790053a0 	strh	w0, [x29, #40]
  400430:	f9001bbf 	str	xzr, [x29, #48]
  400434:	14000056 	b	40058c <main+0x190>
  400438:	a94287a0 	ldp	x0, x1, [x29, #40]
  40043c:	a90387a0 	stp	x0, x1, [x29, #56]
  400440:	a94287a0 	ldp	x0, x1, [x29, #40]
  400444:	a90387a0 	stp	x0, x1, [x29, #56]
  400448:	f9400ba3 	ldr	x3, [x29, #16]
  40044c:	794053a0 	ldrh	w0, [x29, #40]
  400450:	d3402400 	ubfx	x0, x0, #0, #10
  400454:	12003c00 	and	w0, w0, #0xffff
  400458:	d2800202 	mov	x2, #0x10                  	// #16
  40045c:	2a0003e1 	mov	w1, w0
  400460:	aa0303e0 	mov	x0, x3
  400464:	97ffff7f 	bl	400260 <.plt+0x20>
  400468:	b9801fa0 	ldrsw	x0, [x29, #28]
  40046c:	aa0003e1 	mov	x1, x0
  400470:	910043a0 	add	x0, x29, #0x10
  400474:	eb00003f 	cmp	x1, x0
  400478:	54000120 	b.eq	40049c <main+0xa0>  // b.none
  40047c:	794073a0 	ldrh	w0, [x29, #56]
  400480:	d3402400 	ubfx	x0, x0, #0, #10
  400484:	12003c01 	and	w1, w0, #0xffff
  400488:	794053a0 	ldrh	w0, [x29, #40]
  40048c:	d3402400 	ubfx	x0, x0, #0, #10
  400490:	12003c00 	and	w0, w0, #0xffff
  400494:	6b00003f 	cmp	w1, w0
  400498:	54000661 	b.ne	400564 <main+0x168>  // b.any
  40049c:	a94287a0 	ldp	x0, x1, [x29, #40]
  4004a0:	a90487a0 	stp	x0, x1, [x29, #72]
  4004a4:	a94287a0 	ldp	x0, x1, [x29, #40]
  4004a8:	a90587a0 	stp	x0, x1, [x29, #88]
  4004ac:	f9400ba3 	ldr	x3, [x29, #16]
  4004b0:	794053a0 	ldrh	w0, [x29, #40]
  4004b4:	d3402400 	ubfx	x0, x0, #0, #10
  4004b8:	12003c00 	and	w0, w0, #0xffff
  4004bc:	d2800202 	mov	x2, #0x10                  	// #16
  4004c0:	2a0003e1 	mov	w1, w0
  4004c4:	aa0303e0 	mov	x0, x3
  4004c8:	97ffff66 	bl	400260 <.plt+0x20>
  4004cc:	a94287a0 	ldp	x0, x1, [x29, #40]
  4004d0:	a90687a0 	stp	x0, x1, [x29, #104]
  4004d4:	a94287a0 	ldp	x0, x1, [x29, #40]
  4004d8:	a90787a0 	stp	x0, x1, [x29, #120]
  4004dc:	f9400ba3 	ldr	x3, [x29, #16]
  4004e0:	794053a0 	ldrh	w0, [x29, #40]
  4004e4:	d3402400 	ubfx	x0, x0, #0, #10
  4004e8:	12003c00 	and	w0, w0, #0xffff
  4004ec:	d2800202 	mov	x2, #0x10                  	// #16
  4004f0:	2a0003e1 	mov	w1, w0
  4004f4:	aa0303e0 	mov	x0, x3
  4004f8:	97ffff5a 	bl	400260 <.plt+0x20>
  4004fc:	a94287a0 	ldp	x0, x1, [x29, #40]
  400500:	a90687a0 	stp	x0, x1, [x29, #104]
  400504:	a94287a0 	ldp	x0, x1, [x29, #40]
  400508:	a90587a0 	stp	x0, x1, [x29, #88]
  40050c:	f9400ba3 	ldr	x3, [x29, #16]
  400510:	794053a0 	ldrh	w0, [x29, #40]
  400514:	d3402400 	ubfx	x0, x0, #0, #10
  400518:	12003c00 	and	w0, w0, #0xffff
  40051c:	d2800202 	mov	x2, #0x10                  	// #16
  400520:	2a0003e1 	mov	w1, w0
  400524:	aa0303e0 	mov	x0, x3
  400528:	97ffff4e 	bl	400260 <.plt+0x20>
  40052c:	a94287a0 	ldp	x0, x1, [x29, #40]
  400530:	a90487a0 	stp	x0, x1, [x29, #72]
  400534:	a94287a0 	ldp	x0, x1, [x29, #40]
  400538:	a90387a0 	stp	x0, x1, [x29, #56]
  40053c:	f9400ba3 	ldr	x3, [x29, #16]
  400540:	794053a0 	ldrh	w0, [x29, #40]
  400544:	d3402400 	ubfx	x0, x0, #0, #10
  400548:	12003c00 	and	w0, w0, #0xffff
  40054c:	d2800202 	mov	x2, #0x10                  	// #16
  400550:	2a0003e1 	mov	w1, w0
  400554:	aa0303e0 	mov	x0, x3
  400558:	97ffff42 	bl	400260 <.plt+0x20>
  40055c:	52800140 	mov	w0, #0xa                   	// #10
  400560:	14000013 	b	4005ac <main+0x1b0>
  400564:	794053a0 	ldrh	w0, [x29, #40]
  400568:	d3402400 	ubfx	x0, x0, #0, #10
  40056c:	12003c00 	and	w0, w0, #0xffff
  400570:	51000400 	sub	w0, w0, #0x1
  400574:	12003c00 	and	w0, w0, #0xffff
  400578:	12002400 	and	w0, w0, #0x3ff
  40057c:	12003c01 	and	w1, w0, #0xffff
  400580:	794053a0 	ldrh	w0, [x29, #40]
  400584:	33002420 	bfxil	w0, w1, #0, #10
  400588:	790053a0 	strh	w0, [x29, #40]
  40058c:	794053a0 	ldrh	w0, [x29, #40]
  400590:	12002400 	and	w0, w0, #0x3ff
  400594:	12003c00 	and	w0, w0, #0xffff
  400598:	7100001f 	cmp	w0, #0x0
  40059c:	54fff4e1 	b.ne	400438 <main+0x3c>  // b.any
  4005a0:	794073a0 	ldrh	w0, [x29, #56]
  4005a4:	d3402400 	ubfx	x0, x0, #0, #10
  4005a8:	12003c00 	and	w0, w0, #0xffff
  4005ac:	b00003e1 	adrp	x1, 47d000 <__FRAME_END__+0xfd54>
  4005b0:	f947a821 	ldr	x1, [x1, #3920]
  4005b4:	f94047a2 	ldr	x2, [x29, #136]
  4005b8:	f9400021 	ldr	x1, [x1]
  4005bc:	ca010041 	eor	x1, x2, x1
  4005c0:	f100003f 	cmp	x1, #0x0
  4005c4:	54000040 	b.eq	4005cc <main+0x1d0>  // b.none
  4005c8:	94006596 	bl	419c20 <__stack_chk_fail>
  4005cc:	a8c97bfd 	ldp	x29, x30, [sp], #144
  4005d0:	d65f03c0 	ret
  4005d4:	00000000 	.inst	0x00000000 ; undefined

