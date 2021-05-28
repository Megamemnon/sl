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

struct ASTNode *
new_child(struct ASTNode *parent)
{
  struct ASTNode child = {};
  ARRAY_INIT(child.children, child.children_n);

  ARRAY_APPEND(child, parent->children, parent->children_n);

  return &parent->children[parent->children_n - 1];
}
