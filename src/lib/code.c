#include "code.h"

void
free_code_block(struct CodeBlock *code)
{
  ARRAY_FREE(code->instructions);

  free(code->code);
  code->code_length = 0;
}

int
generate_code(const struct CodeGenerator *generator, struct CodeBlock *code)
{
  size_t size = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(code->instructions); ++i)
  {
    const struct CodeInstruction *insr = ARRAY_GET(code->instructions,
      struct CodeInstruction, i);
    size += generator->size_callback(insr);
  }

  code->code = malloc(size);
  unsigned char *write_at = code->code;
  for (size_t i = 0; i < ARRAY_LENGTH(code->instructions); ++i)
  {
    const struct CodeInstruction *insr = ARRAY_GET(code->instructions,
      struct CodeInstruction, i);
    size_t advance = generator->write_callback(write_at, insr);
    write_at += advance;
  }

  return 0;
}
