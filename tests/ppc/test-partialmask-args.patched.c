int g;
int h;

int f(int i, int j) {
  h = g;
  g = j;
  return i + 1;
}

void _start() {
  g = 5;
  g = f(1, 3);
}
