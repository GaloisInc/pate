#include "util.h"

int g = -11;
void f(int* g);

void _start() {
  f(&g);
}

void f(int* g) {
  *g = 56;
}
