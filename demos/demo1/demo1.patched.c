int h(int i){
  return -i;
}

int g(int i){
  return i;
}

int f(int i) {
  // negated conditional
  if (i <= 0) {
    // functions are automatically matched
    return h(i);
  } else {
    return g(i);
  }
}

void _start() {
  f(-1);
}
