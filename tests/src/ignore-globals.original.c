#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void _start() {
  h = 1;
  g = 2;
}
