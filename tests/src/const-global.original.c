#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void f(int a){
  h = a;
}

void test(){
  f(1);
  g = h;
}

void _start() {
  test();
}


