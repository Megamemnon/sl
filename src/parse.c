#include "parse.h"
#include "common.h"
#include <string.h>

typedef ARR(sl_ASTNode) NodeArray;

struct sl_ASTNode
{
  sl_ASTNode *parent;
  Array children;

  sl_ASTNodeType type;
  const struct Token *location;
  char *name;
  char *typename;
  bool atomic;
};

int verbose = 0;

const sl_ASTNode *
sl_node_get_parent(const sl_ASTNode *node)
{
  if (node == NULL)
    return NULL;
  return node->parent;
}

size_t
sl_node_get_child_count(const sl_ASTNode *node)
{
  if (node == NULL)
    return 0;
  return ARRAY_LENGTH(node->children);
}

const sl_ASTNode *
sl_node_get_child(const sl_ASTNode *node, size_t index)
{
  if (node == NULL)
    return NULL;
  if (index >= ARRAY_LENGTH(node->children))
    return NULL;
  return ARRAY_GET(node->children, sl_ASTNode, index);
}

sl_ASTNodeType
sl_node_get_type(const sl_ASTNode *node)
{
  if (node == NULL)
    return sl_ASTNodeType_None;
  return node->type;
}

const struct Token *
sl_node_get_location(const sl_ASTNode *node)
{
  if (node == NULL)
    return NULL;
  return node->location;
}

const char *
sl_node_get_name(const sl_ASTNode *node)
{
  if (node == NULL)
    return NULL;
  return node->name;
}

const char *
sl_node_get_typename(const sl_ASTNode *node)
{
  if (node == NULL)
    return NULL;
  return node->typename;
}

bool
sl_node_get_atomic(const sl_ASTNode *node)
{
  if (node == NULL)
    return FALSE;
  return node->atomic;
}

sl_ASTNode *
sl_node_new()
{
  sl_ASTNode *node = SL_NEW(sl_ASTNode);
  node->parent = NULL;
  node->name = NULL;
  node->typename = NULL;
  ARRAY_INIT(node->children, sl_ASTNode);
  return node;
}

static void
free_children(sl_ASTNode *root)
{
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    free_children(ARRAY_GET(root->children, sl_ASTNode, i));
  }
  ARRAY_FREE(root->children);
  if (root->name != NULL)
    free(root->name);
  if (root->typename != NULL)
    free(root->typename);
}

void
free_tree(sl_ASTNode *root)
{
  /* Recursively free the children of this node. */
  free_children(root);
}

static void
copy_node_and_children(sl_ASTNode *dst, const sl_ASTNode *src)
{
  ARRAY_INIT_WITH_RESERVED(dst->children, sl_ASTNode,
    ARRAY_LENGTH(src->children));
  for (size_t i = 0; i < ARRAY_LENGTH(src->children); ++i)
  {
    sl_ASTNode *dst_child = ARRAY_GET(dst->children, sl_ASTNode, i);
    const sl_ASTNode *src_child =
      ARRAY_GET(src->children, sl_ASTNode, i);
    copy_node_and_children(dst_child, src_child);
    dst_child->parent = dst;
  }
  {
    dst->type = src->type;
    dst->location = src->location;
    if (src->name != NULL)
      dst->name = strdup(src->name);
    else
      dst->name = NULL;

    if (src->typename == NULL)
      dst->typename = strdup(src->typename);
    else
      dst->typename = NULL;
  }
}

void
copy_tree(sl_ASTNode *dst, const sl_ASTNode *src)
{
  sl_ASTNode result = {};
  copy_node_and_children(&result, src);

  free_tree(dst);
  *dst = result;
}

/* TODO */
#if 0
static void
print_children(const sl_ASTNode *root, unsigned int depth,
  print_node_callback_t print_callback)
{
  for (size_t i = 0; i < depth; ++i)
    printf(" ");
  char buf[1024];
  print_callback(buf, 1024, root);
  printf("%s\n", buf);
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    print_children(ARRAY_GET(root->children, sl_ASTNode, i),
      depth + 1, print_callback);
  }
}

void
print_tree(const sl_ASTNode *root, print_node_callback_t print_callback)
{
  print_children(root, 0, print_callback);
}
#endif

sl_ASTNode *
new_child(sl_ASTNode *parent)
{
  sl_ASTNode child = {};
  child.parent = parent;
  ARRAY_INIT(child.children, sl_ASTNode);

  ARRAY_APPEND(parent->children, sl_ASTNode, child);

  return ARRAY_GET(parent->children, sl_ASTNode,
    ARRAY_LENGTH(parent->children) - 1);
}

void
traverse_tree(const sl_ASTNode *root,
  traverse_node_callback_t node_callback, void *user_data)
{
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    traverse_tree(ARRAY_GET(root->children, sl_ASTNode, i), node_callback,
      user_data);
  }
  node_callback(root, user_data);
}

Array *
parser_token_buffer(struct ParserState *state)
{
  return lex_state_front_buffer(state->input);
}

bool
done_parsing(struct ParserState *state)
{
  if (state->token_index >= ARRAY_LENGTH(*parser_token_buffer(state)))
    return TRUE;
  return FALSE;
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
next_is_string(struct ParserState *state)
{
  if (get_current_token(state)->type == TokenTypeStringLiteral)
    return TRUE;
  return FALSE;
}

int
consume_string(struct ParserState *state, const char **string)
{
  if (get_current_token(state)->type == TokenTypeStringLiteral)
  {
    *string = get_current_token(state)->value;
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

static void
free_ast_node(sl_ASTNode *node)
{
  if (node == NULL)
    return;
  if (node->name != NULL)
    free(node->name);
  if (node->typename != NULL)
    free(node->typename);
}

static void
init_ast_node(sl_ASTNode *node)
{
  node->type = sl_ASTNodeType_None;
  node->location = NULL;
  node->name = NULL;
  node->typename = NULL;
  node->atomic = FALSE;
}

static int
parse_namespace(struct ParserState *state);

static int
parse_path(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Path;
  state->ast_current->location = get_current_token(state);

  const char *first_segment;
  if (!consume_identifier(state, &first_segment))
  {
    add_error(state->unit, get_current_token(state),
      "missing first path segment in path to axiom/theorem.");
  }
  else
  {
    add_child_and_descend(state);
    init_ast_node(state->ast_current);
    state->ast_current->location = get_current_token(state);
    state->ast_current->type = sl_ASTNodeType_PathSegment;
    state->ast_current->name = strdup(first_segment);
    ascend(state);
  }

  while (consume_symbol(state, "."))
  {
    const char *segment;
    if (!consume_identifier(state, &segment))
    {
      add_error(state->unit, get_current_token(state),
        "missing path segment following dot '.' in path to axiom/theorem.");
    }
    else
    {
      add_child_and_descend(state);
      init_ast_node(state->ast_current);
      state->ast_current->location = get_current_token(state);
      state->ast_current->type = sl_ASTNodeType_PathSegment;
      state->ast_current->name = strdup(segment);
      ascend(state);
    }
  }

  ascend(state);
  return 0;
}

static int
parse_use(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Use;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "use"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'use' in use statement");
  }

  int err = parse_path(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after use statement");
  }

  ascend(state);
  return 0;
}

static int
parse_type(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Type;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "type"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'type' in type declaration");
  }

  const char *typename;
  if (!consume_identifier(state, &typename))
  {
    add_error(state->unit, get_current_token(state),
      "missing typename in type declaration");
  }
  else
  {
    state->ast_current->typename = strdup(typename);
  }

  if (consume_keyword(state, "atomic"))
  {
    state->ast_current->atomic = TRUE;
  }
  else
  {
    state->ast_current->atomic = FALSE;
  }

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after type declaration");
  }

  ascend(state);
  return 0;
}

static int
parse_value(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->location = get_current_token(state);

  if (consume_symbol(state, "$"))
  {
    /* This is a variable. */
    state->ast_current->type = sl_ASTNodeType_Variable;
    const char *variable_name;
    if (!consume_identifier(state, &variable_name))
    {
      add_error(state->unit, get_current_token(state),
        "missing variable name in value.");
    }
    else
    {
      state->ast_current->name = strdup(variable_name);
    }
  }
  else if (consume_symbol(state, "%"))
  {
    /* This is a placeholder. */
    state->ast_current->type = sl_ASTNodeType_Placeholder;
    const char *placeholder_name;
    if (!consume_identifier(state, &placeholder_name))
    {
      add_error(state->unit, get_current_token(state),
        "missing placeholder name in value.");
    }
    else
    {
      state->ast_current->name = strdup(placeholder_name);
    }
  }
  else
  {
    /* Parse the name of the constant. */
    int err = parse_path(state);
    PROPAGATE_ERROR(err);

    if (consume_symbol(state, "("))
    {
      /* We have a composition. Parse the arguments. */
      state->ast_current->type = sl_ASTNodeType_Composition;

      add_child_and_descend(state);
      init_ast_node(state->ast_current);
      state->ast_current->location = get_current_token(state);
      state->ast_current->type = sl_ASTNodeType_CompositionArgumentList;

      bool first_token = TRUE;
      while (!consume_symbol(state, ")"))
      {
        if (!first_token)
        {
          if (!consume_symbol(state, ","))
          {
            add_error(state->unit, get_current_token(state),
              "missing comma ',' separating arguments in composition.");
          }
        }
        if (first_token)
          first_token = FALSE;

        int err = parse_value(state);
        PROPAGATE_ERROR(err);
      }

      ascend(state);
    }
    else
    {
      /* Just a constant. */
      state->ast_current->type = sl_ASTNodeType_Constant;
    }
  }

  ascend(state);
  return 0;
}

static int
parse_latex(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Latex;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "latex"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'latex' in LaTeX formatting.");
  }

  bool first_token = TRUE;
  while (!consume_symbol(state, ";"))
  {
    if (!first_token)
    {
      if (!consume_symbol(state, "+"))
      {
        add_error(state->unit, get_current_token(state),
          "missing separator '+' between strings of LaTeX formatting.");
      }
    }
    if (first_token)
      first_token = FALSE;
    if (next_is_string(state))
    {
      add_child_and_descend(state);
      init_ast_node(state->ast_current);
      state->ast_current->type = sl_ASTNodeType_LatexString;
      state->ast_current->location = get_current_token(state);
      const char *latex_str;
      if (!consume_string(state, &latex_str))
      {
        add_error(state->unit, get_current_token(state),
          "missing string literal in LaTeX formatting.");
      }
      else
      {
        state->ast_current->name = strdup(latex_str);
      }
      ascend(state);
    }
    else if (consume_symbol(state, "$"))
    {
      /* This is a variable. */
      add_child_and_descend(state);
      init_ast_node(state->ast_current);
      state->ast_current->type = sl_ASTNodeType_LatexVariable;
      state->ast_current->location = get_current_token(state);
      const char *variable_name;
      if (!consume_identifier(state, &variable_name))
      {
        add_error(state->unit, get_current_token(state),
          "missing variable name in latex variable.");
      }
      else
      {
        state->ast_current->name = strdup(variable_name);
      }
      ascend(state);
    }
    else
    {
      int err = parse_value(state);
      PROPAGATE_ERROR(err);
    }
  }

  ascend(state);
  return 0;
}

static int
parse_constant_item(struct ParserState *state)
{
  if (next_is_keyword(state, "latex"))
  {
    int err = parse_latex(state);
    PROPAGATE_ERROR(err);
  }
  else
  {
    add_error(state->unit, get_current_token(state),
      "expected LaTeX formatting.");
    return 1; /* TODO: This should not be fatal. */
  }

  return 0;
}

static int
parse_constant_declaration(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_ConstantDeclaration;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "const"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'const' in constant declaration");
  }

  const char *const_name;
  if (!consume_identifier(state, &const_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing constant name in constant declaration");
  }
  else
  {
    state->ast_current->name = strdup(const_name);
  }

  if (!consume_symbol(state, ":"))
  {
    add_error(state->unit, get_current_token(state),
      "missing colon ':' separating constant name and type in constant declaration");
  }

  int err = parse_path(state);
  PROPAGATE_ERROR(err);

  if (consume_symbol(state, "{"))
  {
    while (!consume_symbol(state, "}"))
    {
      err = parse_constant_item(state);
      PROPAGATE_ERROR(err);
    }
  }
  else if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' or block after constant declaration.");
  }

  ascend(state);
  return 0;
}

static int
parse_parameter_list(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_ParameterList;
  state->ast_current->location = get_current_token(state);

  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "missing symbol '(' in parameter list.");
  }

  bool first_token = TRUE;
  while (!consume_symbol(state, ")"))
  {
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "missing comma ',' separating parameters in parameter list.");
      }
    }
    if (first_token)
      first_token = FALSE;

    add_child_and_descend(state);
    init_ast_node(state->ast_current);
    state->ast_current->type = sl_ASTNodeType_Parameter;
    state->ast_current->location = get_current_token(state);

    const char *parameter_name;
    if (!consume_identifier(state, &parameter_name))
    {
      add_error(state->unit, get_current_token(state),
        "missing parameter name.");
    }
    else
    {
      state->ast_current->name = strdup(parameter_name);
    }

    if (!consume_symbol(state, ":"))
    {
      add_error(state->unit, get_current_token(state),
        "missing colon ':' separating parameter name and type.");
    }

    int err = parse_path(state);
    PROPAGATE_ERROR(err);

    ascend(state);
  }

  ascend(state);

  return 0;
}

static int
parse_bind(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Bind;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "bind"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'bind' in bind statement.");
  }

  int err = parse_value(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after bind statement.");
  }

  ascend(state);
  return 0;
}

static int
parse_expression_item(struct ParserState *state)
{
  if (next_is_keyword(state, "latex"))
  {
    int err = parse_latex(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "bind"))
  {
    int err = parse_bind(state);
    PROPAGATE_ERROR(err);
  }
  else
  {
    add_error(state->unit, get_current_token(state),
      "expected a bind, or LaTeX formatting.");
    return 1; /* TODO: This should not be fatal. */
  }

  return 0;
}

static int
parse_expression(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Expression;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "expr"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'expr' in type declaration.");
  }

  int err = parse_path(state);
  PROPAGATE_ERROR(err);

  const char *expression_name;
  if (!consume_identifier(state, &expression_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing expression name in expression declaration.");
  }
  else
  {
    state->ast_current->name = strdup(expression_name);
  }

  err = parse_parameter_list(state);
  PROPAGATE_ERROR(err);

  if (consume_symbol(state, "{"))
  {
    while (!consume_symbol(state, "}"))
    {
      err = parse_expression_item(state);
      PROPAGATE_ERROR(err);
    }
  }
  else if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' or block after expression declaration.");
  }

  ascend(state);
  return 0;
}

static int
parse_require(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Require;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "require"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'require' in require statement.");
  }

  const char *require_name;
  if (!consume_identifier(state, &require_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing requirement name in require statement.");
  }
  else
  {
    state->ast_current->name = strdup(require_name);
  }

  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "missing symbol '(' in require statement.");
  }

  bool first_token = TRUE;
  while (!consume_symbol(state, ")"))
  {
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "missing comma ',' separating arguments in require statement.");
      }
    }
    if (first_token)
      first_token = FALSE;

    int err = parse_value(state);
    PROPAGATE_ERROR(err);
  }

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after require statement.");
  }

  ascend(state);
  return 0;
}

static int
parse_definition(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Def;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "def"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'def' in definition.");
  }

  const char *definition_name;
  if (!consume_identifier(state, &definition_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing definition name in definition.");
  }
  else
  {
    state->ast_current->name = strdup(definition_name);
  }

  int err = parse_value(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after definition.");
  }

  ascend(state);
  return 0;
}

static int
parse_assume(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Assume;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "assume"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'assume' in assumption.");
  }

  int err = parse_value(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after assumption.");
  }

  ascend(state);
  return 0;
}

static int
parse_infer(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Infer;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "infer"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'infer' in inference.");
  }

  int err = parse_value(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after inference.");
  }

  ascend(state);
  return 0;
}

static int
parse_axiom_item(struct ParserState *state)
{
  if (next_is_keyword(state, "require"))
  {
    int err = parse_require(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "def"))
  {
    int err = parse_definition(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "assume"))
  {
    int err = parse_assume(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "infer"))
  {
    int err = parse_infer(state);
    PROPAGATE_ERROR(err);
  }
  else
  {
    add_error(state->unit, get_current_token(state),
      "expected a definition, assumption, or inference.");
    return 1; /* TODO: This should not be fatal. */
  }

  return 0;
}

static int
parse_axiom(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Axiom;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "axiom"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'axiom' in axiom statement.");
  }

  const char *axiom_name;
  if (!consume_identifier(state, &axiom_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing axiom name in axiom statement.");
  }
  else
  {
    state->ast_current->name = strdup(axiom_name);
  }

  int err = parse_parameter_list(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "missing symbol '{' enclosing axiom statement.");
  }

  while (!consume_symbol(state, "}"))
  {
    err = parse_axiom_item(state);
    PROPAGATE_ERROR(err);
  }

  ascend(state);
  return 0;
}

static int
parse_theorem_reference(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_TheoremReference;
  state->ast_current->location = get_current_token(state);

  int err = parse_path(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "missing symbol '(' in theorem reference.");
  }

  bool first_token = TRUE;
  while (!consume_symbol(state, ")"))
  {
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "missing comma ',' separating arguments in theorem reference arguments.");
      }
    }
    if (first_token)
      first_token = FALSE;

    err = parse_value(state);
    PROPAGATE_ERROR(err);
  }

  ascend(state);
  return 0;
}

static int
parse_step(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Step;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "step"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'step' in step.");
  }

  int err = parse_theorem_reference(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after step.");
  }

  ascend(state);
  return 0;
}

static int
parse_theorem_item(struct ParserState *state)
{
  if (next_is_keyword(state, "require"))
  {
    int err = parse_require(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "def"))
  {
    int err = parse_definition(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "assume"))
  {
    int err = parse_assume(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "infer"))
  {
    int err = parse_infer(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "step"))
  {
    int err = parse_step(state);
    PROPAGATE_ERROR(err);
  }
  else
  {
    add_error(state->unit, get_current_token(state),
      "expected a definition, assumption, inference, or step.");
    return 1; /* TODO: This should not be fatal. */
  }

  return 0;
}

static int
parse_theorem(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Theorem;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "theorem"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'theorem' in theorem statement.");
  }

  const char *theorem_name;
  if (!consume_identifier(state, &theorem_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing theorem name in theorem statement.");
  }
  else
  {
    state->ast_current->name = strdup(theorem_name);
  }

  int err = parse_parameter_list(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "missing symbol '{' enclosing theorem statement.");
  }

  while (!consume_symbol(state, "}"))
  {
    err = parse_theorem_item(state);
    PROPAGATE_ERROR(err);
  }

  ascend(state);
  return 0;
}

static int
parse_namespace_item(struct ParserState *state)
{
  if (next_is_keyword(state, "namespace"))
  {
    int err = parse_namespace(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "use"))
  {
    int err = parse_use(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "type"))
  {
    int err = parse_type(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "const"))
  {
    int err = parse_constant_declaration(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "expr"))
  {
    int err = parse_expression(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "axiom"))
  {
    int err = parse_axiom(state);
    PROPAGATE_ERROR(err);
  }
  else if (next_is_keyword(state, "theorem"))
  {
    int err = parse_theorem(state);
    PROPAGATE_ERROR(err);
  }
  else
  {
    add_error(state->unit, get_current_token(state),
      "expected a type, expression, axiom, or theorem.");
    return 1; /* TODO: This should not be fatal. */
  }

  return 0;
}

static int
parse_namespace(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Namespace;
  state->ast_current->location = get_current_token(state);

  if (!consume_keyword(state, "namespace"))
  {
    add_error(state->unit, get_current_token(state),
      "missing keyword 'namespace' in namespace declaration");
  }

  const char *namespace_name;
  if (!consume_identifier(state, &namespace_name))
  {
    add_error(state->unit, get_current_token(state),
      "missing namespace name in namespace declaration");
  }
  else
  {
    state->ast_current->name = strdup(namespace_name);
  }

  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "missing curly brace '{' in namespace declaration");
  }

  while (!consume_symbol(state, "}"))
  {
    int err = parse_namespace_item(state);
    PROPAGATE_ERROR(err);
  }

  ascend(state);

  return 0;
}

int
parse_root(struct ParserState *state)
{
  state->ast_root = sl_node_new();
  state->ast_current = state->ast_root;

  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  state->ast_current->type = sl_ASTNodeType_Namespace;

  while (tokens_remain(state))
  {
    int err = parse_namespace_item(state);
    PROPAGATE_ERROR(err);
  }

  //ascend(state);
  return 0;
}

static void
print_ast_node(char *buf, size_t len, const sl_ASTNode *node)
{
  switch (node->type)
  {
    case sl_ASTNodeType_None:
      snprintf(buf, len, "Unknown<>");
    case sl_ASTNodeType_Namespace:
      if (node->name == NULL)
        snprintf(buf, len, "Namespace<Unnamed>");
      else
        snprintf(buf, len, "Namespace<\"%s\">",
          node->name);
      break;
    case sl_ASTNodeType_Type:
      snprintf(buf, len, "Type<%s>", node->typename);
      break;
    case sl_ASTNodeType_Expression:
      snprintf(buf, len, "Expression<\"%s\" : %s>",
        node->name, node->typename);
      break;
    case sl_ASTNodeType_Axiom:
      snprintf(buf, len, "Axiom<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Theorem:
      snprintf(buf, len, "Theorem<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Parameter:
      snprintf(buf, len, "Parameter<\"%s\" : %s>",
        node->name, node->typename);
      break;
    case sl_ASTNodeType_Def:
      snprintf(buf, len, "Def<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Assume:
      snprintf(buf, len, "Assume<>");
      break;
    case sl_ASTNodeType_Require:
      snprintf(buf, len, "Require<>");
      break;
    case sl_ASTNodeType_Infer:
      snprintf(buf, len, "Infer<>");
      break;
    case sl_ASTNodeType_Step:
      snprintf(buf, len, "Step<>");
      break;
    case sl_ASTNodeType_Composition:
      snprintf(buf, len, "Composition<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Constant:
      snprintf(buf, len, "Constant<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Variable:
      snprintf(buf, len, "Variable<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Placeholder:
      snprintf(buf, len, "Placeholder<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_TheoremReference:
      snprintf(buf, len, "Theorem Reference<>");
      break;
    case sl_ASTNodeType_Path:
      snprintf(buf, len, "Path<>");
      break;
    case sl_ASTNodeType_PathSegment:
      snprintf(buf, len, "Path Segment<\"%s\">", node->name);
      break;
    default:
      snprintf(buf, len, "");
      break;
  }
}
