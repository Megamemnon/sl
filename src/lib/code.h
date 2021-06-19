#ifndef CODE_H
#define CODE_H

#include "common.h"

enum CPUDataType
{
  CPUDataTypeInt16 = 0,
  CPUDataTypeUnsignedInt16,
  CPUDataTypeInt32,
  CPUDataTypeUnsignedInt32,
  CPUDataTypeInt64,
  CPUDataTypeUnsignedInt64,

  CPUDataTypePointer,
  CPUDataTypeBytes
};

enum CPUInstructionType
{
  CPUInstructionTypeAdd = 0
};

struct CodeInstruction
{

};

struct CodeBlock
{
  Array instructions;

  unsigned char *code;
  size_t code_length;
};

void
free_code_block(struct CodeBlock *code);

typedef size_t (* InstructionSizeCallback)(const struct CodeInstruction *insr);
typedef size_t (* InstructionWriteCallback)(unsigned char *dst,
  const struct CodeInstruction *insr);

struct CodeGenerator
{
  InstructionSizeCallback size_callback;
  InstructionWriteCallback write_callback;
};

int
generate_code(const struct CodeGenerator *generator, struct CodeBlock *code);

#endif
