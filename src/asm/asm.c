#include "asm.h"
#include <lex.h>

const char *asm_keywords[] = {
  NULL
};

const char *asm_symbols[] = {
  "@",
  "(", ")",
  "{", "}",
  ",", ":",
  "'", "\"",
  "/*", "*/",
  "//",
  NULL
};

int
assemble(const char *input_path, FILE *out)
{
  /* Open the file. */
  struct CompilationUnit unit = {};
  open_compilation_unit(&unit, input_path);

  /* Lex the file */
  struct LexState lex_out = {};

  init_lex_state(&lex_out);
  file_to_lines(&lex_out, &unit);
  tokenize_strings(&lex_out, '\'');
  tokenize_strings(&lex_out, '"');
  remove_whitespace(&lex_out);
  tokenize_numeric_literals(&lex_out);
  separate_symbols(&lex_out);
  identify_symbols(&lex_out, asm_symbols);
  remove_block_comments(&lex_out, "/*", "*/");
  remove_line_comments(&lex_out, "//");
  separate_identifiers(&lex_out);
  identify_keywords(&lex_out, asm_keywords);
  remove_line_ends(&lex_out);

  char buf[4096];
  for (size_t i = 0; i < ARRAY_LENGTH(*lex_state_front_buffer(&lex_out)); ++i)
  {
    const struct Token *t = ARRAY_GET(*lex_state_front_buffer(&lex_out),
      struct Token, i);
    snprint_token(buf, 4096, t);
    printf("%s\n", buf);
  }

  /* Clean up */
  free_lex_state(&lex_out);
  close_compilation_unit(&unit);

  return 0;
}
