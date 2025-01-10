#include "util.h"

int X = -11;
int Y = -11;
int OBSERVE __attribute__((section(".output"))) = -12;

#pragma noinline
void g() {
  Y = Y - 1;
}

#pragma noinline
void h() {
  return;
}

#pragma noinline
void f() {
  h();
  if (X < 0 || Y < 0 || X > 100 || Y > 100) {
    return;
  }
  g();
  asm("nop");
  asm("nop");
  asm("nop");
  asm("nop");

  // relation is that X - Y is the same between both programs
  OBSERVE = X - Y;
}

void _start() {
  f();
}
