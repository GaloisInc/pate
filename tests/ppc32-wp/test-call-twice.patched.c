int g;

void f(int i) {
  g = i;
}

void _start() {
  if (g != 1) {
    f(0);
  } else {
    f(1);
  }
}
