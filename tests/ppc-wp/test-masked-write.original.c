int g;
int h;

void f() {
  g = 3;
  h = h + 1;
}

void _start() {
  g = 2;
  h = 1;
  f();
  h = 4;
}
