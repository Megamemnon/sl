#ifndef PARSE_H
#define PARSE_H

#include "lex.h"
#include "common.h"
#include <stdlib.h>

/* Generally parsers need to be written per language, so these are just
   general functions for manipulating ASTs. */
struct ASTNode;

typedef void (* free_node_callback_t)(struct ASTNode *);

 /* Copy the user data from the source to the destination. */
typedef void (* copy_node_callback_t)(struct ASTNode *, const struct ASTNode *);

struct ASTNode
{
  struct ASTNode *parent;
  Array children;

  void *data;

  free_node_callback_t free_callback;
  copy_node_callback_t copy_callback;
};

void
init_tree(struct ASTNode *root);

void
free_tree(struct ASTNode *root);

void
copy_tree(struct ASTNode *dst, const struct ASTNode *src);

typedef void (* print_node_callback_t)(char *, size_t, const struct ASTNode *);

void
print_tree(struct ASTNode *root, print_node_callback_t print_callback);

struct ASTNode *
new_child(struct ASTNode *parent);

typedef void (* traverse_node_callback_t)(const struct ASTNode *, void *);

void
traverse_tree(const struct ASTNode *root, traverse_node_callback_t node_callback,
  void *user_data);

struct ParserError
{
  char *error_msg;
  const struct Token *error_location;
};

struct ParserState
{
  struct CompilationUnit *unit;
  struct LexState *input;
  size_t token_index;

  struct ASTNode ast_root;
  struct ASTNode *ast_current;
};

bool
done_parsing(struct ParserState *state);

Array *
parser_token_buffer(struct ParserState *state);

struct Token *
get_current_token(struct ParserState *state);

void
add_child_and_descend(struct ParserState *state);

void
ascend(struct ParserState *state);

int
advance(struct ParserState *state);

bool
next_keyword(struct ParserState *state, const char *keyword);

int
consume_keyword(struct ParserState *state, const char *keyword);

bool
next_is_keyword(struct ParserState *state, const char *keyword);

int
consume_symbol(struct ParserState *state, const char *symbol);

bool
next_is_symbol(struct ParserState *state, const char *symbol);

int
consume_identifier(struct ParserState *state, const char **identifier);

bool
tokens_remain(struct ParserState *state);

#endif
