#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

int f (int x) {
  int i = 0;
  int v = x;
  int ret = v;
  for(; i<10; i++) {
    x++;
    ret = x;
  }
  ret = x;
  return ret;
}

void _start() {
  g = f(h);
}
