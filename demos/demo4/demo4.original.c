int err;

int div(int i, int j) {
  err = (j == 0);
  return (i / j);
}

void _start() {
  div(4, 2);
}
