unsigned int g = -11;
unsigned int x = -12;

void _start() {
  unsigned int low_bits = x & 0x00000ff0;
  g = low_bits >> 4;
}
