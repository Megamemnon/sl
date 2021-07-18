#include "sl.h"
#include <parse.h>
#include <common.h>

#include <string.h>

int verbose = 0;

#define LOG_NORMAL(out, ...) \
do { \
  fprintf(out, __VA_ARGS__); \
} \
while (0);

#define LOG_VERBOSE(out, ...) \
do { \
  if (verbose) \
    fprintf(out, __VA_ARGS__); \
} \
while (0);

const char *sl_keywords[] = {
  "namespace",

  "atomic",
  "binds",

  "use",
  "type",
  "const",
  "expr",
  "axiom",
  "theorem",

  "assume",
  "require",
  "infer",
  "step",
  "def",
  NULL
};

const char *sl_symbols[] = {
  "(", ")",
  "[", "]",
  "{", "}",
  ".", ",", ";",
  "%", "$", "=",
  "/*", "*/",
  "//",
  NULL
};

enum ASTNodeType
{
  ASTNodeTypeNone = 0,
  ASTNodeTypeNamespace,

  ASTNodeTypeUse,
  ASTNodeTypeType,
  ASTNodeTypeConstantDeclaration,
  ASTNodeTypeExpression,
  ASTNodeTypeAxiom,
  ASTNodeTypeTheorem,

  ASTNodeTypeParameterList,
  ASTNodeTypeParameter,

  ASTNodeTypeBindingList,
  ASTNodeTypeBinding,

  ASTNodeTypeDef,
  ASTNodeTypeAssume,
  ASTNodeTypeRequire,
  ASTNodeTypeInfer,
  ASTNodeTypeStep,

  ASTNodeTypeComposition,
  ASTNodeTypeConstant,
  ASTNodeTypeVariable,
  ASTNodeTypePlaceholder,
  ASTNodeTypeTheoremReference,

  ASTNodeTypeCompositionArgumentList,
  ASTNodeTypePath,

  ASTNodeTypePathSegment
};

struct ASTNodeData
{
  enum ASTNodeType type;
  const struct Token *location;
  char *name;
  char *typename;
  bool atomic;
};

#define AST_NODE_DATA(node) ((struct ASTNodeData *)node->data)

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

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after constant declaration");
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
parse_binding_list(struct ParserState *state)
{
  add_child_and_descend(state);
  init_ast_node(state->ast_current);
  AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeBindingList;
  AST_NODE_DATA(state->ast_current)->location = get_current_token(state);

  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "missing symbol '(' in binding list.");
  }

  bool first_token = TRUE;
  while (!consume_symbol(state, ")"))
  {
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "missing comma ',' separating expressions in binding list.");
      }
    }
    if (first_token)
      first_token = FALSE;

    int err = parse_value(state);
    PROPAGATE_ERROR(err);
  }

  ascend(state);

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

  if (consume_keyword(state, "binds"))
  {
    err = parse_binding_list(state);
    PROPAGATE_ERROR(err);
  }

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after expression declaration.");
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
  if (next_is_keyword(state, "def"))
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
  if (next_is_keyword(state, "def"))
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

static int
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

#include "logic.h"

struct ValidationState
{
  bool valid;
  FILE *out;

  struct CompilationUnit *unit;
  const struct ParserState *input;

  LogicState *logic;
  SymbolPath *prefix_path;
  Array search_paths;
};

static SymbolPath *
lookup_symbol(struct ValidationState *state, const SymbolPath *path)
{
  /* Build a list of candidate absolute paths. */
  SymbolPath **paths = malloc(sizeof(SymbolPath *) *
    (ARRAY_LENGTH(state->search_paths) + 1));
  for (size_t i = 0; i < ARRAY_LENGTH(state->search_paths); ++i)
  {
    const SymbolPath *search_in =
      *ARRAY_GET(state->search_paths, SymbolPath *, i);
    paths[i] = copy_symbol_path(search_in);
    append_symbol_path(paths[i], path);
  }
  paths[ARRAY_LENGTH(state->search_paths)] = NULL;

  SymbolPath *result = find_first_occupied_path(state->logic, paths);

  for (size_t i = 0; i < ARRAY_LENGTH(state->search_paths); ++i)
    free_symbol_path(paths[i]);
  free(paths);

  return result;
}

static SymbolPath *
extract_path(struct ValidationState *state, const struct ASTNode *path)
{
  const struct ASTNodeData *data = AST_NODE_DATA(path);
  if (data->type != ASTNodeTypePath)
  {
    add_error(state->unit, data->location,
      "expected a path but found the wrong type of node.");
    state->valid = FALSE;
    return NULL;
  }

  SymbolPath *dst = init_symbol_path();
  for (size_t i = 0; i < ARRAY_LENGTH(path->children); ++i)
  {
    const struct ASTNode *seg =
      ARRAY_GET(path->children, struct ASTNode, i);
    const struct ASTNodeData *seg_data = AST_NODE_DATA(seg);
    if (seg_data->type != ASTNodeTypePathSegment)
    {
      add_error(state->unit, data->location,
        "expected a path segment but found the wrong type of node.");
      state->valid = FALSE;
      return NULL;
    }
    else
    {
      push_symbol_path(dst, seg_data->name);
    }
  }

  return dst;
}

static SymbolPath *
extract_use(struct ValidationState *state, const struct ASTNode *use)
{
  const struct ASTNodeData *data = AST_NODE_DATA(use);
  if (data->type != ASTNodeTypeUse)
  {
    add_error(state->unit, data->location,
      "expected a use but found the wrong type of node.");
    state->valid = FALSE;
    return NULL;
  }

  if (ARRAY_LENGTH(use->children) != 1)
  {
    add_error(state->unit, data->location,
      "a use node must have a single child, containing a path");
    state->valid = FALSE;
  }

  const struct ASTNode *path = ARRAY_GET(use->children, struct ASTNode, 0);

  return extract_path(state, path);
}

static int
validate_type(struct ValidationState *state,
  const struct ASTNode *type)
{
  const struct ASTNodeData *data = AST_NODE_DATA(type);
  if (data->type != ASTNodeTypeType)
  {
    add_error(state->unit, data->location,
      "expected a type declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  struct PrototypeType proto;

  proto.type_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.type_path, data->typename);

  proto.atomic = data->atomic;

  LogicError err = add_type(state->logic, proto);
  if (err == LogicErrorSymbolAlreadyExists)
  {
    add_error(state->unit, data->location,
      "symbol already exists when declaring type.");
    state->valid = FALSE;
  }

  free_symbol_path(proto.type_path);

  return 0;
}

static int
validate_constant(struct ValidationState *state, const struct ASTNode *constant)
{
  const struct ASTNodeData *data = AST_NODE_DATA(constant);
  if (data->type != ASTNodeTypeConstantDeclaration)
  {
    add_error(state->unit, data->location,
      "expected a constant declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  struct PrototypeConstant proto;

  proto.constant_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.constant_path, data->name);

  if (ARRAY_LENGTH(constant->children) != 1)
  {
    add_error(state->unit, data->location,
      "a constant node must have a single child, containing the path to the constant's type");
    state->valid = FALSE;
  }
  const struct ASTNode *type = ARRAY_GET(constant->children, struct ASTNode, 0);

  SymbolPath *local_path = extract_path(state, type);

  proto.type_path = lookup_symbol(state, local_path);
  free_symbol_path(local_path);

  LogicError err = add_constant(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, data->location,
      "cannot add constant.");
    state->valid = FALSE;
  }

  free_symbol_path(proto.constant_path);
  free_symbol_path(proto.type_path);

  return 0;
}

static int
extract_parameter(struct ValidationState *state,
  const struct ASTNode *parameter, struct PrototypeParameter *dst)
{
  const struct ASTNodeData *data = AST_NODE_DATA(parameter);
  if (data->type != ASTNodeTypeParameter)
  {
    add_error(state->unit, data->location,
      "expected a parameter but found the wrong type of node.");
    state->valid = FALSE;
  }
  dst->name = strdup(data->name);

  if (ARRAY_LENGTH(parameter->children) != 1)
  {
    add_error(state->unit, data->location,
      "a parameter node must have a single child, containing the path to the parameter's type");
    state->valid = FALSE;
  }
  const struct ASTNode *type = ARRAY_GET(parameter->children, struct ASTNode, 0);

  SymbolPath *local_path = extract_path(state, type);

  dst->type = lookup_symbol(state, local_path);
  free_symbol_path(local_path);

  return 0;
}

static int
validate_expression(struct ValidationState *state,
  const struct ASTNode *expression)
{
  const struct ASTNodeData *data = AST_NODE_DATA(expression);
  if (data->type != ASTNodeTypeExpression)
  {
    add_error(state->unit, data->location,
      "expected an expression declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  /* Construct a prototype expression, then try adding it to the logical
     state. */
  struct PrototypeExpression proto;
  proto.expression_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.expression_path, data->name);

  if (ARRAY_LENGTH(expression->children) < 2)
  {
    add_error(state->unit, data->location,
      "an expression node must have at least two children, the path to the expression's type and the list of parameters.");
    state->valid = FALSE;
  }
  const struct ASTNode *type =
    ARRAY_GET(expression->children, struct ASTNode, 0);

  SymbolPath *local_path = extract_path(state, type);
  proto.expression_type = lookup_symbol(state, local_path);
  free_symbol_path(local_path);

  /* TODO: This should be its own function. */
  const struct ASTNode *param_list =
    ARRAY_GET(expression->children, struct ASTNode, 1);
  const struct ASTNodeData *param_list_data = AST_NODE_DATA(param_list);
  if (param_list_data->type != ASTNodeTypeParameterList)
  {
    add_error(state->unit, data->location,
      "expected a parameter list but found the wrong type of node.");
    state->valid = FALSE;
  }

  size_t args_n = ARRAY_LENGTH(param_list->children);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const struct ASTNode *param =
      ARRAY_GET(param_list->children, struct ASTNode, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  LogicError err = add_expression(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, data->location,
      "cannot add expression to logic state.");
    state->valid = FALSE;
  }

  free_symbol_path(proto.expression_path);
  free_symbol_path(proto.expression_type);
  for (size_t i = 0; i < args_n; ++i)
  {
    free(proto.parameters[i]->name);
    free_symbol_path(proto.parameters[i]->type);
    free(proto.parameters[i]);
  }
  free(proto.parameters);

  return 0;
}

struct Definition
{
  char *name;
  Value *value;
};

static void
free_definition(struct Definition *def)
{
  free(def->name);
  free_value(def->value);

}

struct TheoremEnvironment
{
  Array parameters;
  Array definitions;
};

static void
init_theorem_environment(struct TheoremEnvironment *thm)
{
  ARRAY_INIT(thm->parameters, struct PrototypeParameter);
  ARRAY_INIT(thm->definitions, struct Definition);
}

static void
free_theorem_environment(struct TheoremEnvironment *thm)
{
  ARRAY_FREE(thm->parameters);
  for (size_t i = 0; i < ARRAY_LENGTH(thm->definitions); ++i)
  {
    struct Definition *def = ARRAY_GET(thm->definitions, struct Definition, i);
    free_definition(def);
  }
  ARRAY_FREE(thm->definitions);
}

static Value *
extract_value(struct ValidationState *state,
  const struct ASTNode *value, const struct TheoremEnvironment *env)
{
  const struct ASTNodeData *data = AST_NODE_DATA(value);
  if (data->type == ASTNodeTypeComposition)
  {
    /* Locate the corresponding expression, and verify that the types of
       the arguments match. */
    if (ARRAY_LENGTH(value->children) != 2)
    {
      add_error(state->unit, data->location,
        "a composition node must have two children, the path to the expression and a list of arguments.");
      state->valid = FALSE;
    }

    const struct ASTNode *expr =
      ARRAY_GET(value->children, struct ASTNode, 0);
    const struct ASTNode *args_node =
      ARRAY_GET(value->children, struct ASTNode, 1);

    SymbolPath *local_path = extract_path(state, expr);
    SymbolPath *expr_path = lookup_symbol(state, local_path);
    free_symbol_path(local_path);

    const struct ASTNodeData *args_data = AST_NODE_DATA(args_node);
    if (args_data->type != ASTNodeTypeCompositionArgumentList)
    {
      add_error(state->unit, data->location,
        "expected a composition arguments node, but found the wrong type of node.");
      state->valid = FALSE;
    }
    Value **args =
      malloc(sizeof(Value *) * (ARRAY_LENGTH(args_node->children) + 1));
    for (size_t i = 0; i < ARRAY_LENGTH(args_node->children); ++i)
    {
      const struct ASTNode *child =
        ARRAY_GET(args_node->children, struct ASTNode, i);
      args[i] = extract_value(state, child, env);
      if (args[i] == NULL)
      {
        /* TODO: free. */
        return NULL;
      }
    }
    args[ARRAY_LENGTH(args_node->children)] = NULL;

    Value *v = new_composition_value(state->logic, expr_path, args);

    for (size_t i = 0; i < ARRAY_LENGTH(args_node->children); ++i)
    {
      free_value(args[i]);
    }
    free_symbol_path(expr_path);
    free(args);

    return v;
  }
  else if (data->type == ASTNodeTypeConstant)
  {
    if (ARRAY_LENGTH(value->children) != 1)
    {
      add_error(state->unit, data->location,
        "a constant node must have a single child, the path to the constant.");
      state->valid = FALSE;
    }

    const struct ASTNode *path =
      ARRAY_GET(value->children, struct ASTNode, 0);

    SymbolPath *local_path = extract_path(state, path);
    SymbolPath *const_path = lookup_symbol(state, local_path);
    free_symbol_path(local_path);

    Value *v = new_constant_value(state->logic, const_path);

    free_symbol_path(const_path);

    return v;
  }
  else if (data->type == ASTNodeTypeVariable)
  {
    /* Check that this corresponds to a parameter, and copy the corresponding
       type. */
    const struct PrototypeParameter *param = NULL;
    for (size_t i = 0; i < ARRAY_LENGTH(env->parameters); ++i)
    {
      const struct PrototypeParameter *p =
        ARRAY_GET(env->parameters, struct PrototypeParameter, i);
      if (strcmp(p->name, data->name) == 0)
      {
        param = p;
        break;
      }
    }

    if (param == NULL)
    {
      add_error(state->unit, data->location,
        "variable does not correspond to any parameter.");
      state->valid = FALSE;
      return NULL;
    }

    return new_variable_value(state->logic, param->name, param->type);
  }
  else if (data->type == ASTNodeTypePlaceholder)
  {
    /* Look up the corresponding definition. */
    const struct Definition *def = NULL;
    for (size_t i = 0; i < ARRAY_LENGTH(env->definitions); ++i)
    {
      const struct Definition *d =
        ARRAY_GET(env->definitions, struct Definition, i);
      if (strcmp(d->name, data->name) == 0)
      {
        def = d;
        break;
      }
    }

    if (def == NULL)
    {
      add_error(state->unit, data->location,
        "placeholder does not correspond to any definition.");
      state->valid = FALSE;
      return NULL;
    }

    return copy_value(def->value);
  }
  else
  {
    add_error(state->unit, data->location,
      "expected a composition, constant, variable, or placeholder but found the wrong type of node.");
    state->valid = FALSE;
    return NULL;
  }
}

static int
extract_definition(struct ValidationState *state,
  const struct ASTNode *definition, struct TheoremEnvironment *env)
{
  const struct ASTNodeData *data = AST_NODE_DATA(definition);
  if (data->type != ASTNodeTypeDef)
  {
    add_error(state->unit, data->location,
      "expected a definition but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (ARRAY_LENGTH(definition->children) != 1)
  {
    add_error(state->unit, data->location,
      "expected a single child of the definition node to contain the value.");
    state->valid = FALSE;
  }

  const struct ASTNode *value_node =
    ARRAY_GET(definition->children, struct ASTNode, 0);

  struct Definition def;
  def.name = strdup(data->name);
  def.value = extract_value(state, value_node, env);

  if (def.value == NULL)
    return 1;

  ARRAY_APPEND(env->definitions, struct Definition, def);

  return 0;
}

static Value *
extract_assumption(struct ValidationState *state,
  const struct ASTNode *assumption, struct TheoremEnvironment *env)
{
  const struct ASTNodeData *data = AST_NODE_DATA(assumption);
  if (data->type != ASTNodeTypeAssume)
  {
    add_error(state->unit, data->location,
      "expected an assumption declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (ARRAY_LENGTH(assumption->children) != 1)
  {
    add_error(state->unit, data->location,
      "expected a single child of the assumption node to contain the value.");
    state->valid = FALSE;
  }

  const struct ASTNode *value_node =
    ARRAY_GET(assumption->children, struct ASTNode, 0);
  return extract_value(state, value_node, env);
}

static Value *
extract_inference(struct ValidationState *state,
  const struct ASTNode *inference, struct TheoremEnvironment *env)
{
  const struct ASTNodeData *data = AST_NODE_DATA(inference);
  if (data->type != ASTNodeTypeInfer)
  {
    add_error(state->unit, data->location,
      "expected an inference declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (ARRAY_LENGTH(inference->children) != 1)
  {
    add_error(state->unit, data->location,
      "expected a single child of the inference node to contain the value.");
    state->valid = FALSE;
  }

  const struct ASTNode *value_node =
    ARRAY_GET(inference->children, struct ASTNode, 0);
  return extract_value(state, value_node, env);
}

static int
validate_axiom(struct ValidationState *state,
  const struct ASTNode *axiom)
{
  const struct ASTNodeData *data = AST_NODE_DATA(axiom);
  if (data->type != ASTNodeTypeAxiom)
  {
    add_error(state->unit, data->location,
      "expected an axiom statement but found the wrong type of node.");
    state->valid = FALSE;
  }

  /* Construct a prototype theorem, then try adding it to the logical
     state. */
  struct PrototypeTheorem proto;
  proto.theorem_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.theorem_path, data->name);

  size_t assumptions_n = 0;
  size_t inferences_n = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(axiom->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(axiom->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeAssume)
      ++assumptions_n;
    else if (child_data->type == ASTNodeTypeInfer)
      ++inferences_n;
  }
  proto.assumptions =
    malloc(sizeof(Value *) * (assumptions_n + 1));
  proto.inferences =
    malloc(sizeof(Value *) * (inferences_n + 1));

  struct TheoremEnvironment env;
  init_theorem_environment(&env);

  const struct ASTNode *param_list =
    ARRAY_GET(axiom->children, struct ASTNode, 0);
  const struct ASTNodeData *param_list_data = AST_NODE_DATA(param_list);
  if (param_list_data->type != ASTNodeTypeParameterList)
  {
    add_error(state->unit, data->location,
      "expected a parameter list but found the wrong type of node.");
    state->valid = FALSE;
  }

  size_t args_n = ARRAY_LENGTH(param_list->children);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const struct ASTNode *param =
      ARRAY_GET(param_list->children, struct ASTNode, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    ARRAY_APPEND(env.parameters, struct PrototypeParameter,
      *proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  size_t param_index = 0;
  size_t assume_index = 0;
  size_t infer_index = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(axiom->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(axiom->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeDef)
    {
      int err = extract_definition(state, child, &env);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type == ASTNodeTypeAssume)
    {
      proto.assumptions[assume_index] = extract_assumption(state, child, &env);
      ++assume_index;
    }
    else if (child_data->type == ASTNodeTypeInfer)
    {
      proto.inferences[infer_index] = extract_inference(state, child, &env);
      ++infer_index;
    }
  }
  proto.parameters[args_n] = NULL;
  proto.assumptions[assumptions_n] = NULL;
  proto.inferences[inferences_n] = NULL;

  free_theorem_environment(&env);

  LogicError err = add_axiom(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, data->location,
      "cannot add axiom to logic state.");
    state->valid = FALSE;
  }

  free_symbol_path(proto.theorem_path);
  for (size_t i = 0; i < args_n; ++i)
  {
    free(proto.parameters[i]->name);
    free_symbol_path(proto.parameters[i]->type);
    free(proto.parameters[i]);
  }
  for (size_t i = 0; i < assumptions_n; ++i)
  {
    free_value(proto.assumptions[i]);
  }
  for (size_t i = 0; i < inferences_n; ++i)
  {
    free_value(proto.inferences[i]);
  }
  free(proto.parameters);
  free(proto.assumptions);
  free(proto.inferences);

  return 0;
}

static struct PrototypeProofStep *
extract_step(struct ValidationState *state, const struct ASTNode *step,
  struct TheoremEnvironment *env)
{
  struct PrototypeProofStep *dst = malloc(sizeof(struct PrototypeProofStep));

  /* Find the theorem that is being referenced here. */
  const struct ASTNodeData *data = AST_NODE_DATA(step);
  if (data->type != ASTNodeTypeStep)
  {
    add_error(state->unit, data->location,
      "expected a proof step but found the wrong type of node.");
    state->valid = FALSE;
  }
  if (ARRAY_LENGTH(step->children) != 1)
  {
    add_error(state->unit, data->location,
      "a step node must have exactly one child, the theorem reference.");
    state->valid = FALSE;
  }

  const struct ASTNode *thm_ref =
    ARRAY_GET(step->children, struct ASTNode, 0);
  const struct ASTNodeData *thm_ref_data = AST_NODE_DATA(thm_ref);
  if (thm_ref_data->type != ASTNodeTypeTheoremReference)
  {
    add_error(state->unit, thm_ref_data->location,
      "expected a theorem reference but found the wrong type of node.");
    state->valid = FALSE;
  }
  if (ARRAY_LENGTH(thm_ref->children) == 0)
  {
    add_error(state->unit, thm_ref_data->location,
      "a theorem reference must have at least one child, the path to the theorem.");
    state->valid = FALSE;
  }

  const struct ASTNode *thm_path_node =
    ARRAY_GET(thm_ref->children, struct ASTNode, 0);
  SymbolPath *local_path = extract_path(state, thm_path_node);
  dst->theorem_path = lookup_symbol(state, local_path);
  free_symbol_path(local_path);
  dst->arguments = malloc(sizeof(Value *) * (ARRAY_LENGTH(thm_ref->children)));

  /* Next, extract all the arguments being passed to the theorem. */
  for (size_t i = 0; i < ARRAY_LENGTH(thm_ref->children) - 1; ++i)
  {
    const struct ASTNode *arg =
      ARRAY_GET(thm_ref->children, struct ASTNode, i + 1);
    dst->arguments[i] = extract_value(state, arg, env);
  }
  dst->arguments[ARRAY_LENGTH(thm_ref->children) - 1] = NULL;

  return dst;
}

static int
validate_theorem(struct ValidationState *state,
  const struct ASTNode *theorem)
{
  const struct ASTNodeData *data = AST_NODE_DATA(theorem);
  if (data->type != ASTNodeTypeTheorem)
  {
    add_error(state->unit, data->location,
      "expected a theorem statement but found the wrong type of node.");
    state->valid = FALSE;
  }

  /* Construct a prototype theorem, then try adding it to the logical
     state. */
  struct PrototypeTheorem proto;
  proto.theorem_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.theorem_path, data->name);

  size_t assumptions_n = 0;
  size_t inferences_n = 0;
  size_t steps_n = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(theorem->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeAssume)
      ++assumptions_n;
    else if (child_data->type == ASTNodeTypeInfer)
      ++inferences_n;
    else if (child_data->type == ASTNodeTypeStep)
      ++steps_n;
  }
  proto.assumptions =
    malloc(sizeof(Value *) * (assumptions_n + 1));
  proto.inferences =
    malloc(sizeof(Value *) * (inferences_n + 1));
  proto.steps =
    malloc(sizeof(struct PrototypeProofStep) * (steps_n + 1));

  struct TheoremEnvironment env;
  init_theorem_environment(&env);

  const struct ASTNode *param_list =
    ARRAY_GET(theorem->children, struct ASTNode, 0);
  const struct ASTNodeData *param_list_data = AST_NODE_DATA(param_list);
  if (param_list_data->type != ASTNodeTypeParameterList)
  {
    add_error(state->unit, data->location,
      "expected a parameter list but found the wrong type of node.");
    state->valid = FALSE;
  }

  size_t args_n = ARRAY_LENGTH(param_list->children);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const struct ASTNode *param =
      ARRAY_GET(param_list->children, struct ASTNode, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    ARRAY_APPEND(env.parameters, struct PrototypeParameter,
      *proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  size_t assume_index = 0;
  size_t infer_index = 0;
  size_t step_index = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(theorem->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeDef)
    {
      int err = extract_definition(state, child, &env);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type == ASTNodeTypeAssume)
    {
      proto.assumptions[assume_index] = extract_assumption(state, child, &env);
      char *str = string_from_value(proto.assumptions[assume_index]);
      free(str);
      ++assume_index;
    }
    else if (child_data->type == ASTNodeTypeInfer)
    {
      proto.inferences[infer_index] = extract_inference(state, child, &env);
      ++infer_index;
    }
    else if (child_data->type == ASTNodeTypeStep)
    {
      proto.steps[step_index] = extract_step(state, child, &env);
      ++step_index;
    }
  }
  proto.parameters[args_n] = NULL;
  proto.assumptions[assumptions_n] = NULL;
  proto.inferences[inferences_n] = NULL;
  proto.steps[steps_n] = NULL;

  free_theorem_environment(&env);

  LogicError err = add_theorem(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, data->location,
      "cannot add theorem to logic state.");
    state->valid = FALSE;
  }

  free_symbol_path(proto.theorem_path);
  for (size_t i = 0; i < args_n; ++i)
  {
    free(proto.parameters[i]->name);
    free_symbol_path(proto.parameters[i]->type);
    free(proto.parameters[i]);
  }
  for (size_t i = 0; i < assumptions_n; ++i)
  {
    free_value(proto.assumptions[i]);
  }
  for (size_t i = 0; i < inferences_n; ++i)
  {
    free_value(proto.inferences[i]);
  }
  for (size_t i = 0; i < steps_n; ++i)
  {
    free_symbol_path(proto.steps[i]->theorem_path);
    for (Value **v = proto.steps[i]->arguments; *v != NULL; ++v)
      free_value(*v);
    free(proto.steps[i]->arguments);
    free(proto.steps[i]);
  }
  free(proto.parameters);
  free(proto.assumptions);
  free(proto.inferences);
  free(proto.steps);

  return 0;
}

static int
validate_namespace(struct ValidationState *state,
  const struct ASTNode *namespace)
{
  const struct ASTNodeData *data = AST_NODE_DATA(namespace);
  if (data->type != ASTNodeTypeNamespace)
  {
    add_error(state->unit, data->location,
      "expected a namespace but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (data->name != NULL)
  {
    push_symbol_path(state->prefix_path, data->name);
  }

  SymbolPath *search_path = copy_symbol_path(state->prefix_path);
  ARRAY_APPEND(state->search_paths, SymbolPath *, search_path);

  /* Validate all the objects contained in this namespace. */
  Array using_paths;
  ARRAY_INIT(using_paths, SymbolPath *);
  for (size_t i = 0; i < ARRAY_LENGTH(namespace->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(namespace->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    int err;
    switch (child_data->type)
    {
      case ASTNodeTypeNamespace:
        err = validate_namespace(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeUse:
        SymbolPath *use_path = extract_use(state, child);
        ARRAY_APPEND(using_paths, SymbolPath *, use_path);
        ARRAY_APPEND(state->search_paths, SymbolPath *, use_path);
        break;
      case ASTNodeTypeType:
        err = validate_type(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeConstantDeclaration:
        err = validate_constant(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeExpression:
        err = validate_expression(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeAxiom:
        err = validate_axiom(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeTheorem:
        err = validate_theorem(state, child);
        PROPAGATE_ERROR(err);
        break;
      default:
        add_error(state->unit, child_data->location,
          "expected a namespace, use, type, constant, expression, axiom, or theorem, but found the wrong type of node.");
        state->valid = FALSE;
        break;
    }
  }

  for (size_t i = 0; i < ARRAY_LENGTH(using_paths); ++i)
  {
    SymbolPath *path = *ARRAY_GET(using_paths, SymbolPath *, i);
    free_symbol_path(path);
    ARRAY_POP(state->search_paths);
  }
  ARRAY_FREE(using_paths);

  ARRAY_POP(state->search_paths);
  free_symbol_path(search_path);

  if (data->name != NULL)
  {
    pop_symbol_path(state->prefix_path);
  }

  return 0;
}

static int
validate(struct ValidationState *state)
{
  state->logic = new_logic_state(state->out);
  state->prefix_path = init_symbol_path();
  ARRAY_INIT(state->search_paths, SymbolPath *);

  /* The root node should have a child that is the root namespace. */
  const struct ASTNode *root_node = &state->input->ast_root;
  if (ARRAY_LENGTH(root_node->children) == 0)
  {
    add_error(state->unit, NULL,
      "No root namespace provided.");
    state->valid = FALSE;
    return 1;
  }

  const struct ASTNode *root_namespace =
    ARRAY_GET(root_node->children, struct ASTNode, 0);
  int err = validate_namespace(state, root_namespace);
  PROPAGATE_ERROR(err);

  free_logic_state(state->logic);
  free_symbol_path(state->prefix_path);
  ARRAY_FREE(state->search_paths);
  return 0;
}

int
sl_verify(const char *input_path, FILE *out)
{
  /* Open the file. */
  LOG_NORMAL(out, "Validating sl file '%s'.\n", input_path);
  struct CompilationUnit unit = {};
  open_compilation_unit(&unit, input_path);

  /* Lex the file */
  LOG_VERBOSE(out, "Tokenizing.\n");
  struct LexState lex_out = {};

  init_lex_state(&lex_out);
  file_to_lines(&lex_out, &unit);
  remove_whitespace(&lex_out);
  separate_symbols(&lex_out);
  identify_symbols(&lex_out, sl_symbols);
  remove_block_comments(&lex_out, "/*", "*/");
  remove_line_comments(&lex_out, "//");
  separate_identifiers(&lex_out);
  identify_keywords(&lex_out, sl_keywords);
  remove_line_ends(&lex_out);

  /* Parse the file */
  LOG_VERBOSE(out, "Parsing.\n");
  struct ParserState parse_out = {};
  parse_out.unit = &unit;
  parse_out.input = &lex_out;
  parse_out.ast_current = &parse_out.ast_root;

  int err = parse_root(&parse_out);
  if (err)
  {
    print_errors(&unit);
    return 1;
  }
  PROPAGATE_ERROR(err);
  //print_tree(&parse_out.ast_root, &print_ast_node);

  /* Validate the file. */
  LOG_VERBOSE(out, "Validating.\n");
  struct ValidationState validation_out = {};
  validation_out.valid = TRUE;
  validation_out.out = out;
  validation_out.unit = &unit;
  validation_out.input = &parse_out;

  err = validate(&validation_out);
  if (err || !validation_out.valid)
    print_errors(&unit);

  if (validation_out.valid)
  {
    LOG_NORMAL(out, "Valid.\n");
  }
  else
  {
    LOG_NORMAL(out, "Invalid.\n");
  }

  /* Free the AST. */
  LOG_VERBOSE(out, "Done.\n");
  free_tree(&parse_out.ast_root);
  PROPAGATE_ERROR(err);

  free_lex_state(&lex_out);
  close_compilation_unit(&unit);

  return 0;
}
