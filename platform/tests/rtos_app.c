#include <stdio.h>
#include "bedrock.h"

int bedrock_stack_size = 100 * 1024;

BEDROCK_THREAD(shouter) {
  puts("Hello, world!");
  bedrock_yield();
  puts("Encore!");
  bedrock_yield();
  puts("YEAH!");
  bedrock_exit();
}
BEDROCK_WRAP(shouter)

BEDROCK_THREAD(accepter) {
  puts("Listening....");
  bedrock_yield();
  fd_t listener = bedrock_listen(6666);
  bedrock_yield();
  puts("Started listening.");
  fd_t remote = bedrock_accept(listener);
  puts("Got one!");
  bedrock_exit();
}
BEDROCK_WRAP(accepter)

void rtos_main() {
  bedrock_spawn(shouter);
  bedrock_spawn(accepter);
}
