int f(int* i) {
  *i = 1;
  if (*i == 1) {
    return 1;
  } else {
    return 0;
  }
}

int g;

void _start() {
  int *i = &g;
  f(&g);
}
