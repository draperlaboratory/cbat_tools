
main:     file format elf64-x86-64


Disassembly of section .init:

00000000004003c8 <_init>:
  4003c8:	48 83 ec 08          	sub    $0x8,%rsp
  4003cc:	48 8b 05 25 0c 20 00 	mov    0x200c25(%rip),%rax        # 600ff8 <__gmon_start__>
  4003d3:	48 85 c0             	test   %rax,%rax
  4003d6:	74 02                	je     4003da <_init+0x12>
  4003d8:	ff d0                	callq  *%rax
  4003da:	48 83 c4 08          	add    $0x8,%rsp
  4003de:	c3                   	retq   

Disassembly of section .plt:

00000000004003e0 <.plt>:
  4003e0:	ff 35 22 0c 20 00    	pushq  0x200c22(%rip)        # 601008 <_GLOBAL_OFFSET_TABLE_+0x8>
  4003e6:	ff 25 24 0c 20 00    	jmpq   *0x200c24(%rip)        # 601010 <_GLOBAL_OFFSET_TABLE_+0x10>
  4003ec:	0f 1f 40 00          	nopl   0x0(%rax)

00000000004003f0 <memcpy@plt>:
  4003f0:	ff 25 22 0c 20 00    	jmpq   *0x200c22(%rip)        # 601018 <memcpy@GLIBC_2.14>
  4003f6:	68 00 00 00 00       	pushq  $0x0
  4003fb:	e9 e0 ff ff ff       	jmpq   4003e0 <.plt>

Disassembly of section .text:

0000000000400400 <_start>:
  400400:	31 ed                	xor    %ebp,%ebp
  400402:	49 89 d1             	mov    %rdx,%r9
  400405:	5e                   	pop    %rsi
  400406:	48 89 e2             	mov    %rsp,%rdx
  400409:	48 83 e4 f0          	and    $0xfffffffffffffff0,%rsp
  40040d:	50                   	push   %rax
  40040e:	54                   	push   %rsp
  40040f:	49 c7 c0 d0 05 40 00 	mov    $0x4005d0,%r8
  400416:	48 c7 c1 60 05 40 00 	mov    $0x400560,%rcx
  40041d:	48 c7 c7 f0 04 40 00 	mov    $0x4004f0,%rdi
  400424:	ff 15 c6 0b 20 00    	callq  *0x200bc6(%rip)        # 600ff0 <__libc_start_main@GLIBC_2.2.5>
  40042a:	f4                   	hlt    
  40042b:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)

0000000000400430 <_dl_relocate_static_pie>:
  400430:	f3 c3                	repz retq 
  400432:	66 2e 0f 1f 84 00 00 	nopw   %cs:0x0(%rax,%rax,1)
  400439:	00 00 00 
  40043c:	0f 1f 40 00          	nopl   0x0(%rax)

0000000000400440 <deregister_tm_clones>:
  400440:	55                   	push   %rbp
  400441:	b8 30 10 60 00       	mov    $0x601030,%eax
  400446:	48 3d 30 10 60 00    	cmp    $0x601030,%rax
  40044c:	48 89 e5             	mov    %rsp,%rbp
  40044f:	74 17                	je     400468 <deregister_tm_clones+0x28>
  400451:	b8 00 00 00 00       	mov    $0x0,%eax
  400456:	48 85 c0             	test   %rax,%rax
  400459:	74 0d                	je     400468 <deregister_tm_clones+0x28>
  40045b:	5d                   	pop    %rbp
  40045c:	bf 30 10 60 00       	mov    $0x601030,%edi
  400461:	ff e0                	jmpq   *%rax
  400463:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  400468:	5d                   	pop    %rbp
  400469:	c3                   	retq   
  40046a:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

0000000000400470 <register_tm_clones>:
  400470:	be 30 10 60 00       	mov    $0x601030,%esi
  400475:	55                   	push   %rbp
  400476:	48 81 ee 30 10 60 00 	sub    $0x601030,%rsi
  40047d:	48 89 e5             	mov    %rsp,%rbp
  400480:	48 c1 fe 03          	sar    $0x3,%rsi
  400484:	48 89 f0             	mov    %rsi,%rax
  400487:	48 c1 e8 3f          	shr    $0x3f,%rax
  40048b:	48 01 c6             	add    %rax,%rsi
  40048e:	48 d1 fe             	sar    %rsi
  400491:	74 15                	je     4004a8 <register_tm_clones+0x38>
  400493:	b8 00 00 00 00       	mov    $0x0,%eax
  400498:	48 85 c0             	test   %rax,%rax
  40049b:	74 0b                	je     4004a8 <register_tm_clones+0x38>
  40049d:	5d                   	pop    %rbp
  40049e:	bf 30 10 60 00       	mov    $0x601030,%edi
  4004a3:	ff e0                	jmpq   *%rax
  4004a5:	0f 1f 00             	nopl   (%rax)
  4004a8:	5d                   	pop    %rbp
  4004a9:	c3                   	retq   
  4004aa:	66 0f 1f 44 00 00    	nopw   0x0(%rax,%rax,1)

00000000004004b0 <__do_global_dtors_aux>:
  4004b0:	80 3d 79 0b 20 00 00 	cmpb   $0x0,0x200b79(%rip)        # 601030 <__TMC_END__>
  4004b7:	75 17                	jne    4004d0 <__do_global_dtors_aux+0x20>
  4004b9:	55                   	push   %rbp
  4004ba:	48 89 e5             	mov    %rsp,%rbp
  4004bd:	e8 7e ff ff ff       	callq  400440 <deregister_tm_clones>
  4004c2:	c6 05 67 0b 20 00 01 	movb   $0x1,0x200b67(%rip)        # 601030 <__TMC_END__>
  4004c9:	5d                   	pop    %rbp
  4004ca:	c3                   	retq   
  4004cb:	0f 1f 44 00 00       	nopl   0x0(%rax,%rax,1)
  4004d0:	f3 c3                	repz retq 
  4004d2:	0f 1f 40 00          	nopl   0x0(%rax)
  4004d6:	66 2e 0f 1f 84 00 00 	nopw   %cs:0x0(%rax,%rax,1)
  4004dd:	00 00 00 

00000000004004e0 <frame_dummy>:
  4004e0:	55                   	push   %rbp
  4004e1:	48 89 e5             	mov    %rsp,%rbp
  4004e4:	5d                   	pop    %rbp
  4004e5:	eb 89                	jmp    400470 <register_tm_clones>
  4004e7:	66 0f 1f 84 00 00 00 	nopw   0x0(%rax,%rax,1)
  4004ee:	00 00 

00000000004004f0 <main>:
struct Account {
  int balance;
} account, account_copy;


int main(int argc,char ** argv) {
  4004f0:	55                   	push   %rbp
  4004f1:	48 89 e5             	mov    %rsp,%rbp
  4004f4:	48 83 ec 10          	sub    $0x10,%rsp
  4004f8:	48 b8 38 10 60 00 00 	movabs $0x601038,%rax
  4004ff:	00 00 00 
  400502:	48 b9 34 10 60 00 00 	movabs $0x601034,%rcx
  400509:	00 00 00 
  40050c:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  400513:	89 7d f8             	mov    %edi,-0x8(%rbp)
  400516:	48 89 75 f0          	mov    %rsi,-0x10(%rbp)
  //Account* account;
  //Account account_copy;
  account.balance = 2048;
  40051a:	c7 04 25 34 10 60 00 	movl   $0x800,0x601034
  400521:	00 08 00 00 
  memcpy(&account_copy, &account, argc);
  400525:	48 63 55 f8          	movslq -0x8(%rbp),%rdx
  400529:	48 89 c7             	mov    %rax,%rdi
  40052c:	48 89 ce             	mov    %rcx,%rsi
  40052f:	e8 bc fe ff ff       	callq  4003f0 <memcpy@plt>
  if (account_copy.balance)
  400534:	83 3c 25 38 10 60 00 	cmpl   $0x0,0x601038
  40053b:	00 
  40053c:	0f 84 0c 00 00 00    	je     40054e <main+0x5e>
    return 0;
  400542:	c7 45 fc 00 00 00 00 	movl   $0x0,-0x4(%rbp)
  400549:	e9 07 00 00 00       	jmpq   400555 <main+0x65>
  else
    return 1;
  40054e:	c7 45 fc 01 00 00 00 	movl   $0x1,-0x4(%rbp)
}
  400555:	8b 45 fc             	mov    -0x4(%rbp),%eax
  400558:	48 83 c4 10          	add    $0x10,%rsp
  40055c:	5d                   	pop    %rbp
  40055d:	c3                   	retq   
  40055e:	66 90                	xchg   %ax,%ax

0000000000400560 <__libc_csu_init>:
  400560:	41 57                	push   %r15
  400562:	41 56                	push   %r14
  400564:	49 89 d7             	mov    %rdx,%r15
  400567:	41 55                	push   %r13
  400569:	41 54                	push   %r12
  40056b:	4c 8d 25 9e 08 20 00 	lea    0x20089e(%rip),%r12        # 600e10 <__frame_dummy_init_array_entry>
  400572:	55                   	push   %rbp
  400573:	48 8d 2d 9e 08 20 00 	lea    0x20089e(%rip),%rbp        # 600e18 <__init_array_end>
  40057a:	53                   	push   %rbx
  40057b:	41 89 fd             	mov    %edi,%r13d
  40057e:	49 89 f6             	mov    %rsi,%r14
  400581:	4c 29 e5             	sub    %r12,%rbp
  400584:	48 83 ec 08          	sub    $0x8,%rsp
  400588:	48 c1 fd 03          	sar    $0x3,%rbp
  40058c:	e8 37 fe ff ff       	callq  4003c8 <_init>
  400591:	48 85 ed             	test   %rbp,%rbp
  400594:	74 20                	je     4005b6 <__libc_csu_init+0x56>
  400596:	31 db                	xor    %ebx,%ebx
  400598:	0f 1f 84 00 00 00 00 	nopl   0x0(%rax,%rax,1)
  40059f:	00 
  4005a0:	4c 89 fa             	mov    %r15,%rdx
  4005a3:	4c 89 f6             	mov    %r14,%rsi
  4005a6:	44 89 ef             	mov    %r13d,%edi
  4005a9:	41 ff 14 dc          	callq  *(%r12,%rbx,8)
  4005ad:	48 83 c3 01          	add    $0x1,%rbx
  4005b1:	48 39 dd             	cmp    %rbx,%rbp
  4005b4:	75 ea                	jne    4005a0 <__libc_csu_init+0x40>
  4005b6:	48 83 c4 08          	add    $0x8,%rsp
  4005ba:	5b                   	pop    %rbx
  4005bb:	5d                   	pop    %rbp
  4005bc:	41 5c                	pop    %r12
  4005be:	41 5d                	pop    %r13
  4005c0:	41 5e                	pop    %r14
  4005c2:	41 5f                	pop    %r15
  4005c4:	c3                   	retq   
  4005c5:	90                   	nop
  4005c6:	66 2e 0f 1f 84 00 00 	nopw   %cs:0x0(%rax,%rax,1)
  4005cd:	00 00 00 

00000000004005d0 <__libc_csu_fini>:
  4005d0:	f3 c3                	repz retq 

Disassembly of section .fini:

00000000004005d4 <_fini>:
  4005d4:	48 83 ec 08          	sub    $0x8,%rsp
  4005d8:	48 83 c4 08          	add    $0x8,%rsp
  4005dc:	c3                   	retq   
