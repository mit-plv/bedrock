        .section        .rodata
.LC0:
        .string "Bedrock main() returned (should never happen!)\n"
        .text

        .globl sys_abort
        .globl _sys_printInt, sys_printInt
	.global _sys_listen, sys_listen
	.global _sys_accept, sys_accept
	.globl sys_read
	.globl sys_write
        
        .globl main
main:
        movl    $ret, %esi
        jmp     main_main
ret:
        movl    $.LC0, %eax
        movq    %rax, %rdi
        movl    $0, %eax
        call printf
        call _exit

sys_printInt:
        movl	bedrock_heap+4(%rbx), %edi
        pushq   %rsi
        jmp     _sys_printInt

sys_listen:
        movl	bedrock_heap+4(%rbx), %edi
	pushq	%rsi
        pushq   $sys_ret
        jmp     _sys_listen
sys_ret:
	movl	%eax, %edi
	retq

sys_accept:
        movl	bedrock_heap+4(%rbx), %edi
	pushq	%rsi
        pushq   $sys_ret
        jmp     _sys_accept

sys_read:
	pushq	%rsi
        movl	bedrock_heap+4(%rbx), %edi
	movl	bedrock_heap+8(%rbx), %esi
	addl	$bedrock_heap, %esi
	movl	bedrock_heap+12(%rbx), %edx
        pushq   $sys_ret
        jmp     read

sys_write:
	pushq	%rsi
        movl	bedrock_heap+4(%rbx), %edi
	movl	bedrock_heap+8(%rbx), %esi
	addl	$bedrock_heap, %esi
	movl	bedrock_heap+12(%rbx), %edx
        pushq   $sys_ret
        jmp     write
