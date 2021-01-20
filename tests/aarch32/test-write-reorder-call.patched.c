#include "util.h"

int g = -11;
int h = -12;
void f(int* g, int* h);

void _start() {
  f(&g, &h);
}

void f(int* g, int* h){
  if (g != h){
    *h = 1;
    *g = 2;
  }
}
