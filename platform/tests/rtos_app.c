#include <stdio.h>
#include "rtos.h"

int bedrock_stack_size = 100;

THREAD_HANDLER(f) {
  puts("Hello, world!");
  bedrock_yield();
  puts("Encore!");
  bedrock_yield();
  puts("YEAH!");
  bedrock_exit();
} END_THREAD_HANDLER

void rtos_main() {
  bedrock_spawn(f);
  bedrock_spawn(f);
}
