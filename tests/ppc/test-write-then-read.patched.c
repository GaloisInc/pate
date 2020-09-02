#include "util.h"

int g = -11;

void _start() {
  g = 1;
  g = g + 1;

  EXIT();
}
