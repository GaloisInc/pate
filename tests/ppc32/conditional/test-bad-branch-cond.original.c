#include "util.h"

int g = -11;

void _start() {
  if (g == 0 || g == 1 || g == 2) {
    g = 2;
  }
}
