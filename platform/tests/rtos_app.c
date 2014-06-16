#include <stdio.h>
#include "rtos.h"

int rtos_stack_size = 2;

THREAD_HANDLER(f) {
  puts("Hello, world!");
  while(1);
} END_THREAD_HANDLER

void rtos_main() {
  spawn(f);
}
