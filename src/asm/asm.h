#ifndef ASM_H
#define ASM_H

/* FRONTEND for an assembler. The actual assembler is implemented in `lib`. */
enum AssemblerSyntax
{
  AssemblerSyntaxIntel = 0,
  AssemblerSyntaxATT
};

struct Assembler
{
  enum AssemblerSyntax syntax;
};

int
assemble(const char *dst_path, const char *src_path,
  struct Assembler spec);

#endif
