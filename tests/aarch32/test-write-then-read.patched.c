#include "util.h"

int f() {
  int i = 1;
  return i + 1;
}

int g;

void _start() {
  g = f();
}
