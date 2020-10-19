int min;
int max;

void f(int i, int j) {
  max = j;
  min = i;

  if (j < i) {
    min = max;
    max = i;
  }
}

void _start() {
  f(1, -1);
}
