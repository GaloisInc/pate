unsigned int g = -11;
unsigned int x = -12;

void _start() {
  unsigned int y = 0;
  asm volatile (
          "ubfx    %[result], %[value], #4, #8\n\t"
          : [result] "=r" (y)
          : [value]"r" (x)
  );
  g = y;
}
