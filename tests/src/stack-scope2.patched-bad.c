#include "util.h"

int h = -11;
int m = -13;
int g __attribute__((section(".output"))) = -12;

void f() {
  int i = 4;
  int j = 5;
  int k = 6;
  g = 1;
}

void _start() {
  int i = 1;
  int j = 7;
  int k = 3;
  f();
  h = i;
  g = j;
  m = k;
}
