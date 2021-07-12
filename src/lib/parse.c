#include "parse.h"
#include "common.h"

#include <stdio.h>
#include <string.h>

void
init_tree(struct ASTNode *root)
{
  root->parent = NULL;
  ARRAY_INIT(root->children, struct ASTNode);
}

static void
free_children(struct ASTNode *root)
{
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    free_children(ARRAY_GET(root->children, struct ASTNode, i));
  }
  ARRAY_FREE(root->children);
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
  ARRAY_INIT_WITH_RESERVED(dst->children, struct ASTNode,
    ARRAY_LENGTH(src->children));
  for (size_t i = 0; i < ARRAY_LENGTH(src->children); ++i)
  {
    struct ASTNode *dst_child = ARRAY_GET(dst->children, struct ASTNode, i);
    const struct ASTNode *src_child =
      ARRAY_GET(src->children, struct ASTNode, i);
    copy_node_and_children(dst_child, src_child);
    dst_child->parent = dst;
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
print_children(const struct ASTNode *root, unsigned int depth,
  print_node_callback_t print_callback)
{
  for (size_t i = 0; i < depth; ++i)
    printf(" ");
  char buf[1024];
  print_callback(buf, 1024, root);
  printf("%s\n", buf);
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    print_children(ARRAY_GET(root->children, struct ASTNode, i),
      depth + 1, print_callback);
  }
}

void
print_tree(const struct ASTNode *root, print_node_callback_t print_callback)
{
  print_children(root, 0, print_callback);
}

struct ASTNode *
new_child(struct ASTNode *parent)
{
  struct ASTNode child = {};
  child.parent = parent;
  ARRAY_INIT(child.children, struct ASTNode);

  ARRAY_APPEND(parent->children, struct ASTNode, child);

  return ARRAY_GET(parent->children, struct ASTNode,
    ARRAY_LENGTH(parent->children) - 1);
}

void
traverse_tree(const struct ASTNode *root,
  traverse_node_callback_t node_callback, void *user_data)
{
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    traverse_tree(ARRAY_GET(root->children, struct ASTNode, i), node_callback,
      user_data);
  }
  node_callback(root, user_data);
}

bool
done_parsing(struct ParserState *state)
{
  if (state->token_index >= ARRAY_LENGTH(*parser_token_buffer(state)))
    return TRUE;
  return FALSE;
}

Array *
parser_token_buffer(struct ParserState *state)
{
  return lex_state_front_buffer(state->input);
}

struct Token *
get_current_token(struct ParserState *state)
{
  return ARRAY_GET(*lex_state_front_buffer(state->input),
    struct Token, state->token_index);
}

void
add_child_and_descend(struct ParserState *state)
{
  state->ast_current = new_child(state->ast_current);
}

void
ascend(struct ParserState *state)
{
  if (state->ast_current != NULL)
    state->ast_current = state->ast_current->parent;
}

int
advance(struct ParserState *state)
{
  ++state->token_index;
  return 0;
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

bool
next_is_keyword(struct ParserState *state, const char *keyword)
{
  if (get_current_token(state)->type == TokenTypeKeyword
      && strcmp(get_current_token(state)->value, keyword) == 0)
  {
    return TRUE;
  }
  return FALSE;
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

bool
next_is_symbol(struct ParserState *state, const char *symbol)
{
  if (get_current_token(state)->type == TokenTypeSymbol
      && strcmp(get_current_token(state)->value, symbol) == 0)
  {
    return TRUE;
  }
  return FALSE;
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

bool
tokens_remain(struct ParserState *state)
{
  if (state->token_index >= ARRAY_LENGTH(*lex_state_front_buffer(state->input)))
    return FALSE;
  return TRUE;
}
