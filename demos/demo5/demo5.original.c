#include <stdio.h>
#include <stdlib.h>

unsigned int mymax(unsigned int i, unsigned int j) {
  if (i > j) { return i; }
  return j;
}

void demo5(unsigned int x, unsigned int y){
  unsigned int z = mymax(x,y);
  // 0x827c
  if (z == x) { puts("First\n"); /* 0x8298 */ }
  else if (z == y) { puts("Second\n"); /* 0x82b4 */ }
  else { puts("Error\n"); /* 0x82c0 */ }
}

int main(int argc, char *argv[]) {
  int x = atoi(argv[1]);
  int y = atoi(argv[2]);
  demo5((unsigned int)x,(unsigned int)y);
}
