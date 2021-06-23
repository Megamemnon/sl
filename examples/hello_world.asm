@asm(bits: 32, start: 0x7C00)
{
  mov ah, 0x0E
  mov al, 'H'
  int 0x10
  mov al, 'e'
  int 0x10
  mov al, 'l'
  int 0x10
  int 0x10
  mov al, 'o'
  int 0x10

  jmp @here

  @bytes(0x7DFE, 0xAA55)
}
