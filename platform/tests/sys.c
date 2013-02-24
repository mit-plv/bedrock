#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program aborted.");
  exit(0);
}

void _sys_printInt(unsigned n) {
  printf("Bedrock> %u\n", n);
}

unsigned _sys_listen(unsigned port) {
#ifdef DEBUG
  fprintf(stderr, "listen(%u)\n", port);
#endif

  int sock = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in sa;

  if (sock == -1) {
    perror("socket");
    exit(1);
  }

  int one = 1;

  if (setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one))) {
    perror("setsockopt");
    exit(1);
  }

  memset(&sa, 0, sizeof(sa));
  sa.sin_family = AF_INET;
  sa.sin_port = htons(port);
  sa.sin_addr.s_addr = INADDR_ANY;

  if (bind(sock, (struct sockaddr *)&sa, sizeof(sa))) {
    perror("bind");
    exit(1);
  }

  if (listen(sock, 10)) {
    perror("listen");
    exit(1);
  }

#ifdef DEBUG
  fprintf(stderr, "listen(%u) = %u\n", port, sock);
#endif

  return sock;
}

unsigned _sys_accept(unsigned sock) {
#ifdef DEBUG
  fprintf(stderr, "accept(%u)\n", sock);
#endif

  int new_sock = accept(sock, NULL, NULL);

  if (new_sock == -1) {
    perror("accept");
    exit(1);
  }

#ifdef DEBUG
  fprintf(stderr, "accept(%u) = %u\n", sock, new_sock);
#endif

  return new_sock;
}
