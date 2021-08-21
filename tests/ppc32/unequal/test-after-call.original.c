#include "util.h"

int g = -11;

void f(){
  return;
}

void _start() {
  f();
  g = 1;

  EXIT();
}
