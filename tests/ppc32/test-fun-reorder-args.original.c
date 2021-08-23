#include "util.h"

int g = -11;
int f = -13;
int h = -12;

void write_g(int i, int j){
  g = i + j;
}

void write_f(int i){
  f = i;
}

void _start() {
  f = 0;
  g = 0;
  int i = 1;
  if (h > 0) {
    write_g(i, 2);
  } else {
    write_f(i);
  }
}
