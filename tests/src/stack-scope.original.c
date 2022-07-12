#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f() {
  g = 1;
}

void _start() {
  int i = 1;
  int j = 2;
  f();
  h = j;
  g = i;
}
