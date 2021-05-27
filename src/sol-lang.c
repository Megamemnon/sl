#include "sol-lang.h"

#include <string.h>

const char *sol_keywords[] = {
  "section",
  "global"
};
const char *sol_symbols[] = {
  "("
  ")",
  "[",
  "]",
  "{",
  "}",
  "/*",
  "*/"
  "//"
};
const char *sol_line_comment_symbols[] = {
  "//"
};

struct LexSpec
get_sol_lex_spec()
{
  struct LexSpec spec = {};

  spec.keywords = sol_keywords;
  spec.keywords_n = sizeof(sol_keywords) / sizeof(sol_keywords[0]);

  spec.symbols = sol_symbols;
  spec.symbols_n = sizeof(sol_symbols) / sizeof(sol_symbols[0]);

  spec.line_comment_symbols = sol_line_comment_symbols;
  spec.line_comment_symbols_n = sizeof(sol_line_comment_symbols) /
    sizeof(sol_line_comment_symbols[0]);

  return spec;
}

int
sol_verify(const char *file_path)
{
  struct LexSpec lex_spec = get_sol_lex_spec();

  lex_file(file_path, &lex_spec);

  return 0;
}
