#include "sol-lang.h"

#include <string.h>

const char *sol_keywords[] = {
  "namespace",
  "import",
  "formula",
  "Formula",
  "hypothesis",
  "infer",
  "rule",
  "axiom",
  "theorem",
  "step",
  "Var",
  NULL
};
const char *sol_symbols[] = {
  "(", ")",
  "[", "]",
  "{", "}",
  ".", ",", ";", ":",
  "/*", "*/",
  "//",
  NULL
};

#include <stdio.h>

int
sol_verify(const char *file_path)
{
  struct LexResult lex;

  file_to_lines(&lex, file_path);
  remove_whitespace(&lex, &lex);
  separate_symbols(&lex, &lex);
  identify_symbols(&lex, &lex, sol_symbols);
  remove_line_comments(&lex, &lex, "//");
  remove_block_comments(&lex, &lex, "/*", "*/");
  separate_identifiers(&lex, &lex);
  identify_keywords(&lex, &lex, sol_keywords);

  /* TMP: Print out results after lexing. */
  char buf[1024];
  for (size_t i = 0; i < lex.tokens_n; ++i)
  {
    snprint_token(buf, 1024, &lex.tokens[i]);
    printf("%s\n", buf);
  }

  return 0;
}
