int min;
int max;

int f(int i, int j) {
  if (i > j) {
    min = j;
    max = i;
  } else {
    min = i;
    max = j;
  }
}

void _start() {
  f(1, -1);
}
