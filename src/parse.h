#ifndef PARSE_H
#define PARSE_H

#include "lex.h"
#include <stdlib.h>

/* Generally parsers need to be written per language, so these are just
   general functions for manipulating ASTs. */
struct ASTNode;

typedef void (* free_node_callback_t)(struct ASTNode *);

struct ASTNode
{
  struct ASTNode *parent;
  struct ASTNode *children;
  size_t children_n;

  void *data;

  free_node_callback_t free_callback;
};

void
free_tree(struct ASTNode *root);

typedef void (* print_node_callback_t)(char *, size_t, const struct ASTNode *);

void
print_tree(struct ASTNode *root, print_node_callback_t print_callback);

struct ASTNode *
new_child(struct ASTNode *parent);

struct ParserError
{
  char *error_msg;
  const struct Token *error_location;
};

struct ParserState
{
  struct LexResult *input;
  size_t token_index;

  struct ASTNode ast_root;
  struct ASTNode *ast_current;

  struct ParserError *errors;
  size_t errors_n;
};

struct Token *
get_current_token(struct ParserState *state);

void
add_child_and_descend(struct ParserState *state);

void
ascend(struct ParserState *state);

int
consume_keyword(struct ParserState *state, const char *keyword);

int
consume_symbol(struct ParserState *state, const char *symbol);

int
consume_identifier(struct ParserState *state, const char **identifier);

int
add_error(struct ParserState *state, const char *msg);

#endif
