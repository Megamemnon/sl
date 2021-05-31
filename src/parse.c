#include "parse.h"
#include "common.h"

#include <stdio.h>
#include <string.h>

static void
free_children(struct ASTNode *root)
{
  for (size_t i = 0; i < root->children_n; ++i)
  {
    free_children(&root->children[i]);
  }
  ARRAY_FREE(root->children, root->children_n);
  if (root->free_callback != NULL)
    root->free_callback(root);
}

void
free_tree(struct ASTNode *root)
{
  /* Recursively free the children of this node. */
  free_children(root);
}

static void
copy_node_and_children(struct ASTNode *dst, const struct ASTNode *src)
{
  dst->free_callback = src->free_callback;
  dst->copy_callback = src->copy_callback;
  ARRAY_INIT_WITH_SIZE(dst->children, dst->children_n, src->children_n);
  for (size_t i = 0; i < src->children_n; ++i)
  {
    copy_node_and_children(&dst->children[i], &src->children[i]);
    dst->children[i].parent = dst;
  }
  if (dst->copy_callback != NULL)
    dst->copy_callback(dst, src);
}

void
copy_tree(struct ASTNode *dst, const struct ASTNode *src)
{
  struct ASTNode result = {};
  copy_node_and_children(&result, src);

  free_tree(dst);
  *dst = result;
}

static void
print_children(struct ASTNode *root, unsigned int depth,
  print_node_callback_t print_callback)
{
  for (size_t i = 0; i < depth; ++i)
    printf(" ");
  char buf[1024];
  print_callback(buf, 1024, root);
  printf("%s\n", buf);
  for (size_t i = 0; i < root->children_n; ++i)
  {
    print_children(&root->children[i], depth + 1, print_callback);
  }
}

void
print_tree(struct ASTNode *root, print_node_callback_t print_callback)
{
  print_children(root, 0, print_callback);
}

struct ASTNode *
new_child(struct ASTNode *parent)
{
  struct ASTNode child = {};
  child.parent = parent;
  ARRAY_INIT(child.children, child.children_n);

  ARRAY_APPEND(child, parent->children, parent->children_n);

  return &parent->children[parent->children_n - 1];
}

void
traverse_tree(const struct ASTNode *root,
  traverse_node_callback_t node_callback, void *user_data)
{
  for (size_t i = 0; i < root->children_n; ++i)
    traverse_tree(&root->children[i], node_callback, user_data);
  node_callback(root, user_data);
}

struct Token *
get_current_token(struct ParserState *state)
{
  return &state->input->tokens[state->token_index];
}

void
add_child_and_descend(struct ParserState *state)
{
  state->ast_current = new_child(state->ast_current);
}

void
ascend(struct ParserState *state)
{
  state->ast_current = state->ast_current->parent;
}

/* If the current token is the keyword, "consume" it and advance the parser. */
int
consume_keyword(struct ParserState *state, const char *keyword)
{
  if (get_current_token(state)->type == TokenTypeKeyword
      && strcmp(get_current_token(state)->value, keyword) == 0)
  {
    ++state->token_index;
    return 1;
  }
  return 0;
}

int
consume_symbol(struct ParserState *state, const char *symbol)
{
  if (get_current_token(state)->type == TokenTypeSymbol
      && strcmp(get_current_token(state)->value, symbol) == 0)
  {
    ++state->token_index;
    return 1;
  }
  return 0;
}

/* If the current token is an identifier, "consume" it and advance. */
int
consume_identifier(struct ParserState *state, const char **identifier)
{
  if (get_current_token(state)->type == TokenTypeIdentifier)
  {
    *identifier = get_current_token(state)->value;
    ++state->token_index;
    return 1;
  }
  return 0;
}

void
add_error(struct ParserState *state, const char *msg)
{
  struct ParserError error = {};
  error.error_msg = strdup(msg);
  error.error_location = get_current_token(state);

  ARRAY_APPEND(error, state->errors, state->errors_n);
}
