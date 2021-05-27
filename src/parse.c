#include "parse.h"
#include "common.h"

#include <stdio.h>

static void
free_children(struct ASTNode *root)
{
  for (size_t i = 0; i < root->children_n; ++i)
  {
    free_children(&root->children[i]);
  }
  ARRAY_FREE(root->children, root->children_n);
}

void
free_tree(struct ASTNode *root)
{
  /* Recursively free the children of this node. */
  free_children(root);
  free(root);
}

static void
print_children(struct ASTNode *root, unsigned int depth)
{
  for (size_t i = 0; i < depth; ++i)
    printf(" ");
  printf("Node\n");
  for (size_t i = 0; i < root->children_n; ++i)
  {
    print_children(&root->children[i], depth + 1);
  }
}

void
print_tree(struct ASTNode *root)
{
  print_children(root, 0);
}

void
parse(struct ParseResult *dst, const struct LexResult *src,
  parse_node_callback_t callback)
{
  struct ParseResult result = {};
  result.ast_root = malloc(sizeof(struct ASTNode));
  result.ast_root->children = NULL;
  result.ast_root->children_n = 0;

  callback(result.ast_root, &src->tokens[0]);

  if (dst->ast_root != NULL)
    free_tree(dst->ast_root);
  dst->ast_root = result.ast_root;
}
