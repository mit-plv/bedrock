.globl bedrock_stack_size
# Assume the C application has defined here the stack size (in words) for each new thread.

.globl bedrock_heap
.equ heapSize, 1024 * 10
.equ bedrock_stack, bedrock_heap + heapSize * 4
.equ globalSched, bedrock_stack + 50 * 4
.equ globalSp, globalSched + 4
        
# Among other things, this is the address of the global pointer to the scheduler data structure.

# This is where the RTOS system jumps when it's ready to turn over control to the application.
        .globl rtos_main
        .globl app_main
        .global scheduler_exit
app_main:
        # Save starting stack pointer.
        movl %ebx, globalSp
        # Initialize scheduler data structure.
        movl $app_main0, %esi # Bedrock return pointer
        jmp scheduler_init
app_main0:
        call rtos_main
        # Now exit the current "thread".
hithere:
        movl $bedrock_stack, %ebx
        movl $50, (%ebx)
        jmp scheduler_exit

# WRAPPERS FOR THREAD LIBRARY FUNCTIONS

return:
        ret
        
        .globl scheduler_spawn
        .globl bedrock_spawn
bedrock_spawn:
        movl globalSp, %ebx
        movl %edi, 4+bedrock_heap(%ebx)
        movl bedrock_stack_size, %eax
        movl %eax, 8+bedrock_heap(%ebx)
        movl $return, %esi
        jmp scheduler_spawn

        .globl scheduler_exit
        .globl bedrock_exit
bedrock_exit:
        movl globalSp, %ebx
        movl bedrock_stack_size, %eax
        movl %eax, 4+bedrock_heap(%ebx)
        jmp scheduler_exit

afterContextSwitch:
        subl $4, %ebx
        movl %ebx, globalSp
        movl bedrock_heap(%ebx), %esp
        ret
        
        .globl scheduler_yield
        .globl bedrock_yield
bedrock_yield:
        movl globalSp, %ebx
        movl %esp, bedrock_heap(%ebx)
        addl $4, %ebx
        movl $afterContextSwitch, %esi
        jmp scheduler_yield
