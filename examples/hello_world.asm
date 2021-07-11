@program(arch: x86, offset: 0x7C00)
@asm(bits: 32, code: {
  mov @register(name: ah), 0x0E;
  mov @register(name: al), 'H';
  int 0x10;
  mov @register(name: al), 'e';
  int 0x10;
  mov @register(name: al), 'l';
  int 0x10;
  int 0x10;
  mov @register(name: al), 'o';
  int 0x10;

  jmp @here;
})
@bytes(offset: 0xFE, data: [0xAA, 0x55])
