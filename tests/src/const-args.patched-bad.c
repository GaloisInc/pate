#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void _start() {
  f(1);
}

void f(int a){
  g = 2;
  h = 4;
}
