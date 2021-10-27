#include "util.h"

int g = -11;
int h = -12;

void __pate_abort(){
  return;
}

void handle_error(){
  return;
}

void _start() {
  if (h > 0) {
    g = 0;
    __pate_abort();
  } else {
    g = 2;
  }
}
