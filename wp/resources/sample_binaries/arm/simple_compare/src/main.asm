@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
@
@    Return 5
@
@ To compile this:
@
@    arm-linux-gnueabi-as -g main.asm -o main.o
@    arm-linux-gnueabi-ld -entry=main main.o -o main
@
@

@ ----------------------------------------------
    .text

@ ----------------------------------------------
@ The MAIN function
@ ----------------------------------------------
    .global main
    .type main, %function
main:
    mov r0, #5
    bx lr
    .size main, .-main
