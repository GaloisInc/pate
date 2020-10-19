int h(int i){
  return -i;
}

int g(int i){
  return i;
}

int f(int i) {
  if (i <= 0) {
    return h(i);
  } else {
    return g(i);
  }
}

void _start() {
  f(-1);
}
