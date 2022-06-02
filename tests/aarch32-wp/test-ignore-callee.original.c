#include "util.h"

int g = -11;

void f() __attribute__((noinline));
void f(){
  g = 1;
}

void _start() {
  f();

  EXIT();
}
