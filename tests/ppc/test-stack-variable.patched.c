#include "util.h"

int g = -11;
int h = -11;

void _start() {
  h = 1;
  h = 1;
  g = h;

  EXIT();
}
