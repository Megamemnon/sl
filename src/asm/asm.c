#include "asm.h"
#include <lex.h>
#include <parse.h>
#include <string.h>

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

enum NodeType
{
  NodeTypeUnidentified = 0,
  NodeTypeProgram
};

/* Parser Methods */
struct NodeData
{
const struct Token *location;

  enum NodeType type;
};

void
free_node(struct ASTNode *node)
{
  struct NodeData *data = (struct NodeData *)node->data;
  free(data);
}

void
copy_node(struct ASTNode *dst, const struct ASTNode *src)
{
  struct NodeData *dst_data = malloc(sizeof(struct NodeData));
  memset(dst_data, 0, sizeof(struct NodeData));

  const struct NodeData *src_data =
    (const struct NodeData *)src->data;
  dst_data->type = src_data->type;

  dst->data = dst_data;
}

void
init_node(struct ASTNode *node)
{
  node->data = malloc(sizeof(struct NodeData));
  memset(node->data, 0, sizeof(struct NodeData));
  node->free_callback = &free_node;
  node->copy_callback = &copy_node;
}

struct NodeData *
get_node_data(struct ASTNode *node)
{
  return (struct NodeData *)node->data;
}

const struct NodeData *
get_node_data_c(const struct ASTNode *node)
{
  return (const struct NodeData *)node->data;
}

static int
parse_program(struct ParserState *state)
{
  return 0;
}

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
  separate_symbols(&lex_out);
  tokenize_numeric_literals(&lex_out);
  identify_symbols(&lex_out, asm_symbols);
  remove_block_comments(&lex_out, "/*", "*/");
  remove_line_comments(&lex_out, "//");
  separate_identifiers(&lex_out);
  identify_keywords(&lex_out, asm_keywords);
  remove_line_ends(&lex_out);

  /* Parse the file */
  struct ParserState parse_out = {};
  parse_out.unit = &unit;
  parse_out.input = &lex_out;
  parse_out.ast_current = &parse_out.ast_root;

  int err = parse_program(&parse_out);
  if (err)
  {
    /* TODO: handle error and clean up (maybe continue if not fatal?). */
    print_errors(&unit);
  }

  /* Clean up */
  free_lex_state(&lex_out);
  close_compilation_unit(&unit);

  return 0;
}
