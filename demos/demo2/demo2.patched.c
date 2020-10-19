int min;
int max;

void f(int i, int j) {
  // extra unconditional writes
  max = j;
  min = i;

  // swapped conditional
  if (j < i) {
    // equivalence requires 'max == j'
    min = max;
    max = i;
  }
}

void _start() {
  f(1, -1);
}
