#include "util.h"

// dummy implementation
int clock() { return 0; }

int NON_OBSERVE = -11;
int OBSERVE __attribute__((section(".output"))) = -12;
//int OBSERVE = -12;

#pragma noinline
void g() {
  NON_OBSERVE = clock();
}

#pragma noinline
void f() {
  NON_OBSERVE = clock();
  // NON_OBSERVE is not known to be equivalent at this point
  OBSERVE = 2; // observable
}

void _start() {
  f();
}
