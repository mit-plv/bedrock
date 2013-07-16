#include <limits.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>

__attribute__((noreturn)) void sys_abort() {
  puts("Bedrock program terminated.");
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

  if (ioctl(sock, FIONBIO, &one)) {
    perror("ioctl");
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

  int new_sock = accept(sock, NULL, NULL), one = 1;

  if (new_sock == -1) {
    perror("accept");
    exit(1);
  }

  if (ioctl(new_sock, FIONBIO, &one)) {
    perror("ioctl");
    exit(1);
  }

#ifdef DEBUG
  fprintf(stderr, "accept(%u) = %u\n", sock, new_sock);
#endif

  return new_sock;
}

unsigned _sys_read(unsigned sock, void *buf, unsigned count) {
  ssize_t n = read(sock, buf, count);

  if (n == -1) {
    if (errno == ECONNRESET)
      n = 0;
    else {
      perror("read");
      exit(1);
    }
  }

#ifdef DEBUG
  fprintf(stderr, "read(%u, %p, %u) = %u\n", sock, buf, count, n);
#endif

  return n;
}

unsigned _sys_write(unsigned sock, void *buf, unsigned count) {
  ssize_t n = write(sock, buf, count);

  if (n == -1) {
    perror("write");
    exit(1);
  }

#ifdef DEBUG
  fprintf(stderr, "write(%u, %p, %u) = %u\n", sock, buf, count, n);
#endif

  return n;
}

static unsigned epoll, num_fds, num_outstanding;
static uint32_t *fds;

static void init_epoll() {
  if (epoll == 0) {
    epoll = epoll_create(1);

    if (epoll == -1) {
      perror("epoll_create");
      exit(1);
    }

    fds = malloc(0);
  }
}

unsigned _sys_declare(unsigned sock, unsigned mode) {
  init_epoll();

  if (sock >= num_fds) {
    fds = realloc(fds, sizeof(uint32_t) * (sock+1));
    memset(fds + num_fds, 0, sizeof(uint32_t) * (sock+1 - num_fds));
    num_fds = sock;
  }

  uint32_t mask = mode ? EPOLLOUT : EPOLLIN;

  if (fds[sock] & mask)
    return UINT_MAX;

  int is_new = 0;

  if (fds[sock] == 0) {
    ++num_outstanding;
    is_new = 1;
  }

  fds[sock] |= mask;

  struct epoll_event event;

  event.events = fds[sock];
  event.data.fd = sock;

  if (epoll_ctl(epoll, is_new ? EPOLL_CTL_ADD : EPOLL_CTL_MOD, sock, &event)) {
    perror("epoll_ctl");
    exit(1);
  }

  unsigned index = 2 * sock + (mode ? 1 : 0);

#ifdef DEBUG
  fprintf(stderr, "declare(%u, %u) = %u\n", sock, mode, index);
#endif

  return index;
}

unsigned _sys_wait(unsigned blocking) {
  if (num_outstanding == 0)
    return UINT_MAX;

  init_epoll();

  struct epoll_event event;
  int count = epoll_wait(epoll, &event, 1, blocking ? -1 : 0);

  if (count == -1) {
    perror("epoll_wait");
    exit(1);
  }

  if (count == 0)
    return UINT_MAX;

  int fd = event.data.fd;
  uint32_t mask = (event.events & EPOLLIN) ? EPOLLIN : EPOLLOUT;

  fds[fd] &= ~mask;

  if (fds[fd] == 0)
    --num_outstanding;

  event.events = fds[fd];

  if (epoll_ctl(epoll, (fds[fd] == 0) ? EPOLL_CTL_DEL : EPOLL_CTL_MOD, fd, &event)) {
    perror("epoll_ctl");
    exit(1);
  }

  unsigned index = 2 * fd + ((mask == EPOLLIN) ? 0 : 1);

#ifdef DEBUG
  fprintf(stderr, "wait(%u) = %u\n", blocking, index);
#endif

  return index;
}

void _sys_close(unsigned fd) {
  if (fd < num_fds && fds[fd]) {
    fds[fd] = 0;
    --num_outstanding;
  }

  if (close(fd) == -1) {
    perror("close");
    exit(1);
  }
}
