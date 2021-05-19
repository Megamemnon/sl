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
  "-"
};

struct ParseSpec
get_asm_parse_spec()
{
  struct ParseSpec spec = {};

  spec.keywords = asm_keywords;
  spec.keywords_n = sizeof(asm_keywords) / sizeof(asm_keywords[0]);

  spec.symbols = asm_symbols;
  spec.symbols_n = sizeof(asm_symbols) / sizeof(asm_symbols[0]);

  return spec;
}

struct LanguageSpec
get_asm_spec()
{
  struct LanguageSpec spec = {};
  spec.get_parse = &get_asm_parse_spec;
  return spec;
}
