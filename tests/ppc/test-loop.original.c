int g;

void f() {
  int i = 0;
  while (i < 10) {
    g = i + g;
    i++;
  }
}

void _start() {
  f();
}
