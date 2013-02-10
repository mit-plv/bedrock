#include <stdlib.h>
#include <stdio.h>

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program aborted.");
  exit(0);
}

void _sys_printInt(unsigned n) {
  printf("Bedrock> %u\n", n);
}
