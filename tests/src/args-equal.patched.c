#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f(int a, int b) {
  h = a;
  g = b;
}

void _start() {
  f(5, 2);
  f(6, 4);
}
