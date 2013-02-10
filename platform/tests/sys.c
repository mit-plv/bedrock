#include <stdlib.h>
#include <stdio.h>

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program aborted.");
  exit(0);
}
