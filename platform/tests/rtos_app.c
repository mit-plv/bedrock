#include <stdio.h>
#include "bedrock.h"

int bedrock_stack_size = 100;

BEDROCK_THREAD(f) {
  puts("Hello, world!");
  bedrock_yield();
  puts("Encore!");
  bedrock_yield();
  puts("YEAH!");
  bedrock_exit();
} END_THREAD

void rtos_main() {
  bedrock_spawn(f);
  bedrock_spawn(f);
}
