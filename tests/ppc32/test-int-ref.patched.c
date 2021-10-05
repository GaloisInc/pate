int f(int* i) {
  *i = 1;
  return 1;
}

int g;

void _start() {
  int *i = &g;
  f(&g);
}
