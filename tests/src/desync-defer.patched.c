#include "util.h"

// dummy implementation
int write(int fd, const void *buf, int nbyte) { return nbyte; }
void *malloc(int size) { char *ptr; return ptr; }

int fd = 1;
int NON_OBSERVE = -11;
int OBSERVE __attribute__((section(".output"))) = -12;
char buf[] = "32";

#pragma noinline
void g(int i) {
  NON_OBSERVE = i;
}

#pragma noinline
void f() {
  OBSERVE = 0;
  char* ignoreme = "45";
  buf[0] = '0';
  buf[1] = '1';
  write(fd, buf, 2);
  buf[0] = '2';
  buf[1] = '3';
  write(fd, buf, 2);
  OBSERVE = 1;
  g(2);
}

void _start() {
  f();
}
