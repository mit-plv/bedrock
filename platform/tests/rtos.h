typedef void (*thread_entry_point)(void);

void bedrock_spawn(thread_entry_point);
__attribute__((noreturn)) void bedrock_exit();

#define RTOS_SETUP_THREAD asm("movl %ebx, bedrock_heap + (1024 * 10 + 50 + 1)*4"); asm("movl bedrock_stack_size, %esp"); asm("shll $2, %esp"); asm("addl %ebx, %esp"); asm("addl $bedrock_heap, %esp")
#define THREAD_HANDLER(name) __attribute__((noreturn)) void name() { RTOS_SETUP_THREAD;
#define END_THREAD_HANDLER }
