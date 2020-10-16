#include "util.h"

int g = -11;
int b = 0;

void _start() {
  b = g < 10 && g > 0;
}
