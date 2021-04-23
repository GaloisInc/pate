#include "util.h"

unsigned int g = -11;
int f = -12;
unsigned int h = -13;

void _start() {
  if (f == 0 || f == 1 || f == 2) {
    h = h >> 1;
  }
  g = g >> 1;
}
