int g;
int f(int* i);

void _start() {
  int *i = &g;
  f(&g);
}

int f(int* i) {
  *i = 1;
  if (*i == 1) {
    return 1;
  } else {
    return 0;
  }
}


