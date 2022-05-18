#include "util.h"

int h = -11;
int g __attribute__((section(".output"))) = -12;

void _start() {
  if(h > 0) {
    if(h > 1) {
      g = g + 1;
    }
  }
}
