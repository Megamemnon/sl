#ifndef PARSE_H
#define PARSE_H

#include <stdlib.h>

/* Generally parsers need to be written per language, so these are just
   general functions for manipulating ASTs. */

struct ASTNode
{
  struct ASTNode *children;
  size_t children_n;
};

void
free_tree(struct ASTNode *root);

void
print_tree(struct ASTNode *root);

struct ASTNode *
new_child(struct ASTNode *parent);

#endif
