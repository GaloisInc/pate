#include "util.h"

int g = -11;
int h = -12;

void write_g1(){
  g = 1;
}

void write_g2(){
  g = 2;
}

void _start() {
  if (h > 0) {
    write_g1();
  } else {
    write_g2();
  }
}
