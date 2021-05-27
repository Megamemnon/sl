#include "sol-lang.h"
#include "parse.h"

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

static void
parse_node(struct ASTNode *parent, const struct Token *token)
{

}

int
sol_verify(const char *file_path)
{
  /* Lex the file */
  struct LexResult lex_out = {};

  file_to_lines(&lex_out, file_path);
  remove_whitespace(&lex_out, &lex_out);
  separate_symbols(&lex_out, &lex_out);
  identify_symbols(&lex_out, &lex_out, sol_symbols);
  remove_line_comments(&lex_out, &lex_out, "//");
  remove_block_comments(&lex_out, &lex_out, "/*", "*/");
  separate_identifiers(&lex_out, &lex_out);
  identify_keywords(&lex_out, &lex_out, sol_keywords);
  remove_line_ends(&lex_out, &lex_out);

  /* Parse the file */
  struct ParseResult parse_out = {};

  parse(&parse_out, &lex_out, &parse_node);

  /* TMP: Print the AST to console. */
  print_tree(parse_out.ast_root);

  return 0;
}
