int err;

int div(int i, int j) {
  // correctly diverges when 'j == 0'
  if (j == 0) {
    err = 1;
    return 0;
  }
  return (i / j);
}

void _start() {
  div(4, 2);
}
