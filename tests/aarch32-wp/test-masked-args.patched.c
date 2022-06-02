int g;
int h;

int f(int i) {
  h = g;
  return i + 1;
}

void _start() {
  g = 3;
  h = 5;
  g = f(1);
  h = 4;
}
