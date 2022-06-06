#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f(){
  h = 3;
}

void test(){
  h = 1;
  f();
  g = h;
}

void _start() {
  test();
}
