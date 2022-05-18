#include "util.h"

int g;

void _start() {
  int i;
  int j;
  int k;
  k = (int)(&i) + (int)(&j);
  g = 1;
} 
