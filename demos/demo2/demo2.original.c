int min;
int max;

int f(int i, int j) {
  max = j;
  min = i;

  if (i < j) {
    min = max;
    max = j;
  }
}

void _start() {
  f(1, -1);
}
