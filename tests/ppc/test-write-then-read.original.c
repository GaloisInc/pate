#include "util.h"

int f() {
  int i = 1;
  return i * 2;
}

int g;

void _start() {
  g = f();
}
