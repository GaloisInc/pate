int g;
int h;

void f() {
  g = 3;
  h = h + 1;
}

void _start() {
  g = 1;
  h = 2;
  f();
  h = 4;
}
