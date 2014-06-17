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
  char buf[1024];

  puts("Listening....");
  bedrock_yield();
  fd_t listener = bedrock_listen(6666);
  bedrock_yield();
  puts("Started listening.");
  fd_t remote = bedrock_accept(listener);
  puts("Got one!");
  bedrock_write(remote, "How's it going?\n", 16);
  unsigned size = bedrock_read(remote, buf, sizeof buf);
  if (size == 0) {
    puts("Uh oh!");
    bedrock_exit();
  }
  bedrock_write(remote, buf, size);
  bedrock_close(remote);
  bedrock_close(listener);
  bedrock_exit();
}
BEDROCK_WRAP(accepter)

void rtos_main() {
  bedrock_spawn(shouter);
  bedrock_spawn(accepter);
}
