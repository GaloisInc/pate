int min;
int max;

void f(int i, int j) {
  if (j > i) {
    min = i;
    max = j;
  } else {
    min = j;
    max = i;
  }
}

void _start() {
  f(1, -1);
}
