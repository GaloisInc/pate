#include "util.h"

int h = -11;
int m = -13;
int g __attribute__((section(".output"))) = -12;

void f() {
  int i = 9;
  int j = 10;
  int k = 11;
  g = 1;
}

void _start() {
  int i = 7;
  int j = 2;
  int k = 8;
  f();
  h = i;
  g = j;
  m = k;
}
