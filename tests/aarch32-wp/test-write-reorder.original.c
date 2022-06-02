#include "util.h"

int g = -11;
int h = -12;

void _start() {
  if (g != h) {
    g = 2;
    h = 1;
  }
}
