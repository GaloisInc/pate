#include "util.h"
static const char HELLO[] __attribute__((section(".output"))) = "hello";

void f();
void _start() {
  f(HELLO);
}

// dummy implementation
int clock() { return 0; }
int puts(const char *str) { return 0; }


int NON_OBSERVE = -11;

#pragma noinline
int g() {
  return clock();
}

#pragma noinline
void f() { 
  NON_OBSERVE = 1;
  puts(HELLO);
}