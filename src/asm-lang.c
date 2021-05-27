#include "asm-lang.h"

#include <string.h>

const char *asm_keywords[] = {
  "section",
  "global"
};
const char *asm_symbols[] = {
  ".",
  ":",
  ";",
  "$",
  "-",
  "//"
};
const char *asm_line_comment_symbols[] = {
  ";",
  "//"
};

struct LexSpec
get_asm_lex_spec()
{
  struct LexSpec spec = {};

  spec.keywords = asm_keywords;
  spec.keywords_n = sizeof(asm_keywords) / sizeof(asm_keywords[0]);

  spec.symbols = asm_symbols;
  spec.symbols_n = sizeof(asm_symbols) / sizeof(asm_symbols[0]);

  spec.line_comment_symbols = asm_line_comment_symbols;
  spec.line_comment_symbols_n = sizeof(asm_line_comment_symbols) /
    sizeof(asm_line_comment_symbols[0]);

  return spec;
}
