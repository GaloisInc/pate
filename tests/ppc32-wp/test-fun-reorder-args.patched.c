#include "util.h"

int g = -11;
int f = -13;
int h = -12;


void write_f(int i){
  f = i;
}

void write_g(int i, int j){
  g = i + j;
}

void _start() {
  f = 0;
  g = 0;
  if (h <= 0) {
    write_f(1);
  } else {
    write_g(1, 2);
  }
}
