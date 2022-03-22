#include "util.h"

int g = -11;

void f() __attribute__((noinline));
void f(){
  g = 2;
}

void _start() {
  f();

  EXIT();
}
