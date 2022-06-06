#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f(){
  // write a different value to h here
  // from the original program
  h = 4;
}

void test(){
  h = 2;
  f();
  // h is not equivalent between the two programs
  // and so this write to g is observably different
  g = h;
}

void _start() {
  test();
}
