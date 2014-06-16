typedef void (*thread_entry_point)(void);

void spawn(thread_entry_point);

#define RTOS_SETUP_THREAD asm("movl %ebx, bedrock_heap + (1024 * 10 + 50 + 1)*4"); asm("movl rtos_stack_size, %esp"); asm("shll $2, %esp"); asm("addl %ebx, %esp"); asm("addl $bedrock_heap, %esp")
#define THREAD_HANDLER(name) __attribute__((noreturn)) void name() { RTOS_SETUP_THREAD;
#define END_THREAD_HANDLER }
