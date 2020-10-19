int g;

void f() {
  int i = 0;
  for(i = 0; i < 10; i++){
    g = g + i;
  }
}

void _start() {
  f();
}
