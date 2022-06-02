#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f(int i) {
  g = i;
}

void _start() {
  if (g == 1) {
    f(1);
  } else {
    f(0);
  }
}
