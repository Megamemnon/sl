#ifndef PARSE_H
#define PARSE_H

#include <stdlib.h>

#include "lex.h"

struct ASTNode
{
  struct ASTNode *children;
  size_t children_n;
};

void
free_tree(struct ASTNode *root);

void
print_tree(struct ASTNode *root);

struct ParseResult
{
  struct ASTNode *ast_root;
};

typedef void (* parse_node_callback_t)(struct ASTNode *parent,
  const struct Token *token);

void
parse(struct ParseResult *dst, const struct LexResult *src,
  parse_node_callback_t callback);

#endif
