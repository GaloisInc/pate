int leq(int i, int j) {
  // diverges if i == j
  if (i <= j) {
    return 1;
  } else {
    return 0;
  }
}

void _start() {
  leq(1, 2);
}
