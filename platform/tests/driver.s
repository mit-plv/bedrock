        .section        .rodata
.LC0:
        .string "Execution complete\n"
        .text

        .globl main
main:
        movl    $ret, %ecx
        jmp     main_main
ret:
        movl    $.LC0, %eax
        movq    %rax, %rdi
        movl    $0, %eax
        call printf
        call _exit
