#include "util.h"

int g = -11;
int f = -12;
int h = -13;

void _start() {
  if (f == 0) {
    h = h >> 1;
  }
  if (f == 1) {
    h = 3;
  }
  g = g >> 1;
}
