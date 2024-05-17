#include "util.h"
void f();
void _start() {
  f();
}

// dummy implementation
int clock() { return 0; }
int puts(const char *str) { return 0; }

int NON_OBSERVE = -11;
int OBSERVE __attribute__((section(".output"))) = -12;
//int OBSERVE = -12;

#pragma noinline
int g() {
  return clock();
}

#pragma noinline
void f() {
  NON_OBSERVE = 1;
  puts("hello");
}