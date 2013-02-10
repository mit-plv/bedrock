        .section        .rodata
.LC0:
        .string "Bedrock main() returned (should never happen!)\n"
        .text

        .globl sys_abort
        
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
