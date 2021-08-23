int g;

void f(int i) {
  g = i;
}

void _start() {
  if (g == 1) {
    f(1);
  } else {
    f(0);
  }
}
