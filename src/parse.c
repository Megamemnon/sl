#include "parse.h"
#include "common.h"

#include <string.h>

int verbose = 0;

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
free_ast_node(struct ASTNode *node)
{
  struct ASTNodeData *data = AST_NODE_DATA(node);
  if (data->name != NULL)
    free(data->name);
  if (data->typename != NULL)
    free(data->typename);
  free(data);
}

static void
copy_ast_node(struct ASTNode *dst, const struct ASTNode *src)
{
  struct ASTNodeData *dst_data = AST_NODE_DATA(src);
  const struct ASTNodeData *src_data = AST_NODE_DATA(src);

  dst_data->type = src_data->type;
  dst_data->location = src_data->location;
  if (src_data->name != NULL)
    dst_data->name = strdup(src_data->name);
  else
    dst_data->name = NULL;

  if (src_data->typename == NULL)
    dst_data->typename = strdup(src_data->typename);
  else
    dst_data->typename = NULL;
}

static void
init_ast_node(struct ASTNode *node)
{
  node->data = malloc(sizeof(struct ASTNodeData));

  struct ASTNodeData *data = AST_NODE_DATA(node);
  data->type = ASTNodeTypeNone;
  data->location = NULL;
  data->name = NULL;
  data->typename = NULL;
  data->atomic = FALSE;

  node->free_callback = &free_ast_node;
  node->copy_callback = &copy_ast_node;
}

static int
parse_namespace(struct ParserState *state);

static int
parse_path(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypePath;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->location = get_current_token(state);
    AST_NODE_DATA(state->ast_current)->type = ASTNodeTypePathSegment;
    AST_NODE_DATA(state->ast_current)->name = strdup(first_segment);
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
      AST_NODE_DATA(state->ast_current)->location = get_current_token(state);
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypePathSegment;
      AST_NODE_DATA(state->ast_current)->name = strdup(segment);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeUse;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeType;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->typename = strdup(typename);
  }

  if (consume_keyword(state, "atomic"))
  {
    AST_NODE_DATA(state->ast_current)->atomic = TRUE;
  }
  else
  {
    AST_NODE_DATA(state->ast_current)->atomic = FALSE;
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
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

  if (consume_symbol(state, "$"))
  {
    /* This is a variable. */
    AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeVariable;
    const char *variable_name;
    if (!consume_identifier(state, &variable_name))
    {
      add_error(state->unit, get_current_token(state),
        "missing variable name in value.");
    }
    else
    {
      AST_NODE_DATA(state->ast_current)->name = strdup(variable_name);
    }
  }
  else if (consume_symbol(state, "%"))
  {
    /* This is a placeholder. */
    AST_NODE_DATA(state->ast_current)->type = ASTNodeTypePlaceholder;
    const char *placeholder_name;
    if (!consume_identifier(state, &placeholder_name))
    {
      add_error(state->unit, get_current_token(state),
        "missing placeholder name in value.");
    }
    else
    {
      AST_NODE_DATA(state->ast_current)->name = strdup(placeholder_name);
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
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeComposition;

      add_child_and_descend(state);
      init_ast_node(state->ast_current);
      AST_NODE_DATA(state->ast_current)->location = get_current_token(state);
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeCompositionArgumentList;

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
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeConstant;
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeLatex;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeLatexString;
      AST_NODE_DATA(state->ast_current)->location = get_current_token(state);
      const char *latex_str;
      if (!consume_string(state, &latex_str))
      {
        add_error(state->unit, get_current_token(state),
          "missing string literal in LaTeX formatting.");
      }
      else
      {
        AST_NODE_DATA(state->ast_current)->name = strdup(latex_str);
      }
      ascend(state);
    }
    else if (consume_symbol(state, "$"))
    {
      /* This is a variable. */
      add_child_and_descend(state);
      init_ast_node(state->ast_current);
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeLatexVariable;
      AST_NODE_DATA(state->ast_current)->location = get_current_token(state);
      const char *variable_name;
      if (!consume_identifier(state, &variable_name))
      {
        add_error(state->unit, get_current_token(state),
          "missing variable name in latex variable.");
      }
      else
      {
        AST_NODE_DATA(state->ast_current)->name = strdup(variable_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeConstantDeclaration;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(const_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeParameterList;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeParameter;
    AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

    const char *parameter_name;
    if (!consume_identifier(state, &parameter_name))
    {
      add_error(state->unit, get_current_token(state),
        "missing parameter name.");
    }
    else
    {
      AST_NODE_DATA(state->ast_current)->name = strdup(parameter_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeBind;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeExpression;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(expression_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeRequire;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(require_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeDef;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(definition_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeAssume;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeInfer;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeAxiom;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(axiom_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeTheoremReference;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeStep;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeTheorem;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(theorem_name);
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
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeNamespace;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

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
    AST_NODE_DATA(state->ast_current)->name = strdup(namespace_name);
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
  init_tree(&state->ast_root);

  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeNamespace;

  while (tokens_remain(state))
  {
    int err = parse_namespace_item(state);
    PROPAGATE_ERROR(err);
  }

  //ascend(state);
  return 0;
}

static void
print_ast_node(char *buf, size_t len, const struct ASTNode *node)
{
  if (node->data == NULL)
  {
    snprintf(buf, len, "");
    return;
  }
  switch (AST_NODE_DATA(node)->type)
  {
    case ASTNodeTypeNone:
      snprintf(buf, len, "Unknown<>");
    case ASTNodeTypeNamespace:
      if (AST_NODE_DATA(node)->name == NULL)
        snprintf(buf, len, "Namespace<Unnamed>");
      else
        snprintf(buf, len, "Namespace<\"%s\">",
          AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeType:
      snprintf(buf, len, "Type<%s>", AST_NODE_DATA(node)->typename);
      break;
    case ASTNodeTypeExpression:
      snprintf(buf, len, "Expression<\"%s\" : %s>",
        AST_NODE_DATA(node)->name, AST_NODE_DATA(node)->typename);
      break;
    case ASTNodeTypeAxiom:
      snprintf(buf, len, "Axiom<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeTheorem:
      snprintf(buf, len, "Theorem<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeParameter:
      snprintf(buf, len, "Parameter<\"%s\" : %s>",
        AST_NODE_DATA(node)->name, AST_NODE_DATA(node)->typename);
      break;
    case ASTNodeTypeDef:
      snprintf(buf, len, "Def<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeAssume:
      snprintf(buf, len, "Assume<>");
      break;
    case ASTNodeTypeRequire:
      snprintf(buf, len, "Require<>");
      break;
    case ASTNodeTypeInfer:
      snprintf(buf, len, "Infer<>");
      break;
    case ASTNodeTypeStep:
      snprintf(buf, len, "Step<>");
      break;
    case ASTNodeTypeComposition:
      snprintf(buf, len, "Composition<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeConstant:
      snprintf(buf, len, "Constant<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeVariable:
      snprintf(buf, len, "Variable<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypePlaceholder:
      snprintf(buf, len, "Placeholder<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    case ASTNodeTypeTheoremReference:
      snprintf(buf, len, "Theorem Reference<>");
      break;
    case ASTNodeTypePath:
      snprintf(buf, len, "Path<>");
      break;
    case ASTNodeTypePathSegment:
      snprintf(buf, len, "Path Segment<\"%s\">", AST_NODE_DATA(node)->name);
      break;
    default:
      snprintf(buf, len, "");
      break;
  }
}
