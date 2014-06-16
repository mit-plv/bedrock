#include <stdio.h>
#include "rtos.h"

int bedrock_stack_size = 100;

THREAD_HANDLER(f) {
  puts("Hello, world!");
  bedrock_exit();
} END_THREAD_HANDLER

void rtos_main() {
  bedrock_spawn(f);
}
