#include "util.h"

unsigned int g = -11;
int f = -12;
unsigned int h = -13;

void _start() {
  if (f == 0) {
    h = h >> 1;
  }
  g = g >> 1;
}
