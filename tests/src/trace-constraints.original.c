#include "util.h"

void _start();

int h;
int f;
int i;
int dump;
int g __attribute__((section(".output"))) = -12;
int j __attribute__((section(".output"))) = -12;

void _start() {
  dump = h;
  dump = i;

  if (h == 0){
    g = f;
  }
  j = i;
}
