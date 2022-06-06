#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f(){
  // re-establish equality here
  h = 3;
}

void test(){
  // write a different h value initially
  h = 2;
  f();
  // f() has re-established equality on h
  // so this observable write is equal
  g = h;
}

void _start() {
  test();
}
