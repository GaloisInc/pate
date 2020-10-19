int g(int i){
  return i;
}

int h(int i){
  return -i;
}

int f(int i) {
  if (i > 0) {
    return g(i);
  } else {
    return h(i);
  }
}

void _start() {
  f(-1);
}
