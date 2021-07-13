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

  "type",
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

  ASTNodeTypeType,
  ASTNodeTypeExpression,
  ASTNodeTypeAxiom,
  ASTNodeTypeTheorem,

  ASTNodeTypeParameter,
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

  ASTNodeTypePath,

  ASTNodeTypePathSegment
};

struct ASTNodeData
{
  enum ASTNodeType type;
  const struct Token *location;
  char *name;
  char *typename;
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

  node->free_callback = &free_ast_node;
  node->copy_callback = &copy_ast_node;
}

static int
parse_namespace(struct ParserState *state);

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

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after type declaration");
  }

  ascend(state);
  return 0;
}

static int
parse_parameter_list(struct ParserState *state)
{
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

    const char *parameter_type;
    if (!consume_identifier(state, &parameter_type))
    {
      add_error(state->unit, get_current_token(state),
        "missing parameter type.");
    }
    else
    {
      AST_NODE_DATA(state->ast_current)->typename = strdup(parameter_type);
    }

    ascend(state);
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

  const char *expression_type;
  if (!consume_identifier(state, &expression_type))
  {
    add_error(state->unit, get_current_token(state),
      "missing resulting expression type in expression declaration.");
  }
  else
  {
    AST_NODE_DATA(state->ast_current)->typename = strdup(expression_type);
  }

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

  int err = parse_parameter_list(state);
  PROPAGATE_ERROR(err);

  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "missing semicolon ';' after expression declaration.");
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
    /* This is either a constant or a composition. */
    const char *constant_name;
    if (!consume_identifier(state, &constant_name))
    {
      /* TODO: change error message to depend on whether this is a
         constant or a composition. */
      add_error(state->unit, get_current_token(state),
        "missing constant name in value.");
    }
    else
    {
      AST_NODE_DATA(state->ast_current)->name = strdup(constant_name);
    }

    if (consume_symbol(state, "("))
    {
      /* We have a composition. Parse the arguments. */
      AST_NODE_DATA(state->ast_current)->type = ASTNodeTypeComposition;

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
  else if (next_is_keyword(state, "type"))
  {
    int err = parse_type(state);
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

#if 0
static struct Symbol *
lookup_symbol(struct ValidationState *state, const struct SymbolPath *path)
{
  /* In order to locate the symbol, make a list of all the possible global paths
     that this symbol could be referring to, depending on the namespace we are
     in. */
  struct SymbolPath prefix_path;
  copy_symbol_path(&prefix_path, &state->prefix_path);

  while (TRUE)
  {
    struct SymbolPath target_path;
    init_symbol_path(&target_path);
    append_symbol_path(&target_path, &prefix_path);
    append_symbol_path(&target_path, path);

    for (size_t i = 0; i < ARRAY_LENGTH(state->symbol_table); ++i)
    {
      struct Symbol *symbol = ARRAY_GET(state->symbol_table, struct Symbol, i);
      if (symbol_paths_equal(&symbol->path, &target_path))
      {
        free_symbol_path(&target_path);
        free_symbol_path(&prefix_path);
        return symbol;
      }
    }

    free_symbol_path(&target_path);
    if (length_of_symbol_path(&prefix_path) == 0)
      break;
    pop_symbol_path(&prefix_path);
  }
  free_symbol_path(&prefix_path);
  return NULL;
}

static int
extract_parameter(struct ValidationState *state,
  const struct ASTNode *parameter, Array *parameter_list)
{
  const struct ASTNodeData *data = AST_NODE_DATA(parameter);
  struct Parameter param = {};
  if (data->type != ASTNodeTypeParameter)
  {
    add_error(state->unit, data->location,
      "expected a parameter but found the wrong type of node.");
    state->valid = FALSE;
  }
  param.name = strdup(data->name);

  struct SymbolPath type_path;
  init_symbol_path(&type_path);
  push_symbol_path(&type_path, data->typename);
  struct Symbol *type = lookup_symbol(state, &type_path);
  if (type == NULL)
  {
    add_error(state->unit, data->location,
      "unknown type in parameter to expression.");
    state->valid = FALSE;
  }
  if (type->type != SymbolTypeType)
  {
    add_error(state->unit, data->location,
      "Type provided as type of expression argument is not a type.");
    state->valid = FALSE;
  }
  param.type = (struct ObjectType *)type->object;
  free_symbol_path(&type_path);

  ARRAY_APPEND(*parameter_list, struct Parameter, param);

  return 0;
}

struct Definition
{
  char *name;
  struct Value value;
};

static void
free_definition(struct Definition *def)
{
  free(def->name);
  free_value(&def->value);
}

struct ProofEnvironment
{
  Array parameters;
  Array definitions;
  Array proven;
};

static void
init_proof_environment(struct ProofEnvironment *env)
{
  ARRAY_INIT(env->parameters, struct Parameter);
  ARRAY_INIT(env->definitions, struct Definition);
  ARRAY_INIT(env->proven, struct Value);
}

static void
free_proof_environment(struct ProofEnvironment *env)
{
  for (size_t i = 0; i < ARRAY_LENGTH(env->parameters); ++i)
  {
    struct Parameter *param =
      ARRAY_GET(env->parameters, struct Parameter, i);
    free_parameter(param);
  }
  ARRAY_FREE(env->parameters);

  for (size_t i = 0; i < ARRAY_LENGTH(env->definitions); ++i)
  {
    struct Definition *def =
      ARRAY_GET(env->definitions, struct Definition, i);
    free_definition(def);
  }
  ARRAY_FREE(env->definitions);

  for (size_t i = 0; i < ARRAY_LENGTH(env->proven); ++i)
  {
    struct Value *v =
      ARRAY_GET(env->proven, struct Value, i);
    free_value(v);
  }
  ARRAY_FREE(env->proven);
}

static int
extract_value(struct ValidationState *state,
  const struct ASTNode *value, struct Value *dst,
  const struct ProofEnvironment *env)
{
  const struct ASTNodeData *data = AST_NODE_DATA(value);
  if (data->type == ASTNodeTypeComposition)
  {
    /* Locate the corresponding expression, and verify that the types of
       the arguments match. */
    struct SymbolPath expr_path;
    init_symbol_path(&expr_path);
    push_symbol_path(&expr_path, data->name);
    const struct Symbol *sym = lookup_symbol(state, &expr_path);
    free_symbol_path(&expr_path);
    if (sym == NULL)
    {
      add_error(state->unit, data->location,
        "unknown expression referenced.");
      state->valid = FALSE;
      return 1;
    }
    if (sym->type != SymbolTypeExpression)
    {
      add_error(state->unit, data->location,
        "compositions must reference expressions.");
      state->valid = FALSE;
      return 1;
    }
    const struct ObjectExpression *expr =
      (struct ObjectExpression *)sym->object;

    /* Go over the children. */
    if (ARRAY_LENGTH(expr->parameters) != ARRAY_LENGTH(value->children))
    {
      add_error(state->unit, data->location,
        "incorrect number of arguments supplied to expression.");
      state->valid = FALSE;
      return 1;
    }
    dst->name = strdup(data->name);
    dst->type = ValueTypeComposition;
    dst->object_type = expr->type;
    ARRAY_INIT(dst->arguments, struct Value);
    for (size_t i = 0; i < ARRAY_LENGTH(value->children); ++i)
    {
      const struct Parameter *param =
        ARRAY_GET(expr->parameters, struct Parameter, i);
      const struct ASTNode *child =
        ARRAY_GET(value->children, struct ASTNode, i);

      struct Value child_value;
      int err = extract_value(state, child, &child_value, env);
      PROPAGATE_ERROR(err);
      if (!types_equal(param->type, child_value.object_type))
      {
        add_error(state->unit, data->location,
          "arguments to composition do not match types.");
        state->valid = FALSE;
        return 1;
      }
      ARRAY_APPEND(dst->arguments, struct Value, child_value);
    }
  }
  else if (data->type == ASTNodeTypeConstant)
  {
    /* TODO: implement constants. */
  }
  else if (data->type == ASTNodeTypeVariable)
  {
    /* Check that this corresponds to a parameter, and copy the corresponding
       type. */
    const struct Parameter *param = NULL;
    for (size_t i = 0; i < ARRAY_LENGTH(env->parameters); ++i)
    {
      const struct Parameter *p =
        ARRAY_GET(env->parameters, struct Parameter, i);
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
      return 1;
    }

    dst->name = strdup(data->name);
    dst->type = ValueTypeVariable;
    dst->object_type = param->type;
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
      return 1;
    }

    copy_value(dst, &def->value);
  }
  else
  {
    add_error(state->unit, data->location,
      "expected a composition, constant, variable, or placeholder but found the wrong type of node.");
    state->valid = FALSE;
    return 1;
  }
  return 0;
}

static int
extract_definition(struct ValidationState *state,
  const struct ASTNode *definition, struct ProofEnvironment *env)
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
  struct Value value;
  int err = extract_value(state, value_node, &value, env);
  PROPAGATE_ERROR(err);

  struct Definition def;
  def.name = strdup(data->name);
  def.value = value;

  ARRAY_APPEND(env->definitions, struct Definition, def);

  return 0;
}

static int
extract_assumption(struct ValidationState *state,
  const struct ASTNode *assumption, struct Theorem *thm,
  struct ProofEnvironment *env)
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
  struct Value value;
  int err = extract_value(state, value_node, &value, env);
  PROPAGATE_ERROR(err);

  ARRAY_APPEND(thm->assumptions, struct Value, value);

  return 0;
}

static int
extract_inference(struct ValidationState *state,
  const struct ASTNode *inference, struct Theorem *thm,
  struct ProofEnvironment *env)
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
  struct Value value;
  int err = extract_value(state, value_node, &value, env);
  PROPAGATE_ERROR(err);

  ARRAY_APPEND(thm->inferences, struct Value, value);

  return 0;
}

static int
validate_axiom(struct ValidationState *state, const struct ASTNode *axiom)
{
  const struct ASTNodeData *data = AST_NODE_DATA(axiom);
  if (data->type != ASTNodeTypeAxiom)
  {
    add_error(state->unit, data->location,
      "expected an axiom statement but found the wrong type of node.");
    state->valid = FALSE;
  }

  struct Symbol sym = {};

  init_symbol_path(&sym.path);
  append_symbol_path(&sym.path, &state->prefix_path);

  struct SymbolPath local_path;
  init_symbol_path(&local_path);
  push_symbol_path(&local_path, data->name);
  append_symbol_path(&sym.path, &local_path);
  if (lookup_symbol(state, &local_path) != NULL)
  {
    add_error(state->unit, data->location,
      "axiom name already in use.");
    state->valid = FALSE;
  }
  free_symbol_path(&local_path);

  sym.type = SymbolTypeTheorem;

  struct Theorem *thm =
    malloc(sizeof(struct Theorem));
  thm->name = strdup(data->name);

  /* First, extract parameters. */
  ARRAY_INIT(thm->parameters, struct Parameter);
  for (size_t i = 0; i < ARRAY_LENGTH(axiom->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(axiom->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeParameter)
    {
      int err = extract_parameter(state, child, &thm->parameters);
      PROPAGATE_ERROR(err);
    }
  }
  sym.object = thm;

  /* Then extract assumptions and inferences. */
  struct ProofEnvironment env;
  init_proof_environment(&env);
  for (size_t i = 0; i < ARRAY_LENGTH(thm->parameters); ++i)
  {
    const struct Parameter *param =
      ARRAY_GET(thm->parameters, struct Parameter, i);
    struct Parameter copy;
    copy_parameter(&copy, param);
    ARRAY_APPEND(env.parameters, struct Parameter, copy);
  }

  ARRAY_INIT(thm->assumptions, struct Value);
  ARRAY_INIT(thm->inferences, struct Value);
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
      int err = extract_assumption(state, child, thm, &env);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type == ASTNodeTypeInfer)
    {
      int err = extract_inference(state, child, thm, &env);
      PROPAGATE_ERROR(err);
    }
  }

  free_proof_environment(&env);
  ARRAY_APPEND(state->symbol_table, struct Symbol, sym);

  return 0;
}

static int
extract_path(struct ValidationState *state, const struct ASTNode *path,
  struct SymbolPath *dst)
{
  const struct ASTNodeData *data = AST_NODE_DATA(path);
  if (data->type != ASTNodeTypePath)
  {
    add_error(state->unit, data->location,
      "expected a path but found the wrong type of node.");
    state->valid = FALSE;
  }

  init_symbol_path(dst);
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
    }
    else
    {
      push_symbol_path(dst, seg_data->name);
    }
  }

  return 0;
}

static int
instantiate_value(struct ValidationState *state, struct Value *dst,
  const struct Value *src, Array args)
{
  switch (src->type)
  {
    case ValueTypeConstant:
      copy_value(dst, src);
      break;
    case ValueTypeVariable:
      /* Find the corresponding argument. */
      {
        const struct Definition *arg = NULL;
        for (size_t i = 0; i < ARRAY_LENGTH(args); ++i)
        {
          const struct Definition *a =
            ARRAY_GET(args, struct Definition, i);
          if (strcmp(a->name, src->name) == 0)
          {
            arg = a;
            break;
          }
        }
        if (arg == NULL)
        {
          add_error(state->unit, NULL,
            "not all arguments supplied for instantiation of value.");
          state->valid = FALSE;
          return 1;
        }
        copy_value(dst, &arg->value);
      }
      break;
    case ValueTypeComposition:
      dst->name = strdup(src->name);
      dst->type = ValueTypeComposition;
      dst->object_type = src->object_type;
      ARRAY_INIT(dst->arguments, struct Value);
      for (size_t i = 0; i < ARRAY_LENGTH(src->arguments); ++i)
      {
        const struct Value *arg =
          ARRAY_GET(src->arguments, struct Value, i);
        struct Value instantiated_arg;
        int err = instantiate_value(state, &instantiated_arg, arg, args);
        PROPAGATE_ERROR(err);
        ARRAY_APPEND(dst->arguments, struct Value, instantiated_arg);
      }
      break;
  }
  return 0;
}

static bool
statement_proven(const struct Value *stmt, const struct ProofEnvironment *env)
{
  for (size_t i = 0; i < ARRAY_LENGTH(env->proven); ++i)
  {
    const struct Value *proven = ARRAY_GET(env->proven, struct Value, i);
    if (values_equal(stmt, proven))
      return TRUE;
  }
  return FALSE;
}

static int
instantiate_theorem(struct ValidationState *state,
  const struct Theorem *src, Array args, struct ProofEnvironment *env)
{
  /* First, instantiate the assumptions. */
  Array instantiated_assumptions;
  ARRAY_INIT(instantiated_assumptions, struct Value);
  for (size_t i = 0; i < ARRAY_LENGTH(src->assumptions); ++i)
  {
    const struct Value *assumption =
      ARRAY_GET(src->assumptions, struct Value, i);
    struct Value instantiated;
    int err = instantiate_value(state, &instantiated, assumption, args);
    PROPAGATE_ERROR(err);
    ARRAY_APPEND(instantiated_assumptions, struct Value, instantiated);
  }

  /* Verify that each assumption has been proven. */
  for (size_t i = 0; i < ARRAY_LENGTH(instantiated_assumptions); ++i)
  {
    struct Value *assumption =
      ARRAY_GET(instantiated_assumptions, struct Value, i);
    if (!statement_proven(assumption, env))
    {
      add_error(state->unit, NULL,
        "assumption not proven while instantiating theorem.");
      state->valid = FALSE;
    }
    free_value(assumption);
  }
  ARRAY_FREE(instantiated_assumptions);

  /* Add all the inferences to the environment as proven statements. */
  for (size_t i = 0; i < ARRAY_LENGTH(src->inferences); ++i)
  {
    const struct Value *inference =
      ARRAY_GET(src->inferences, struct Value, i);
    struct Value instantiated;
    int err = instantiate_value(state, &instantiated, inference, args);
    PROPAGATE_ERROR(err);
    ARRAY_APPEND(env->proven, struct Value, instantiated);
  }

  return 0;
}

static int
validate_step(struct ValidationState *state, const struct ASTNode *step,
  struct Theorem *thm, struct ProofEnvironment *env)
{
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
      "a theorem reference must have at least on child, the path to the theorem.");
    state->valid = FALSE;
  }

  const struct ASTNode *thm_path =
    ARRAY_GET(thm_ref->children, struct ASTNode, 0);
  struct SymbolPath path;
  extract_path(state, thm_path, &path);
  const struct Symbol *ref = lookup_symbol(state, &path);
  if (ref == NULL)
  {
    add_error(state->unit, data->location,
      "proof step references unknown theorem/axiom.");
    state->valid = FALSE;
  }
  free_symbol_path(&path);
  if (ref->type != SymbolTypeTheorem)
  {
    add_error(state->unit, data->location,
      "proof step references object that is not a theorem/axiom.");
    state->valid = FALSE;
  }
  const struct Theorem *referenced = (struct Theorem *)ref->object;

  /* Next, extract all the arguments being passed to the theorem, and check
     that the types match. */
  if (ARRAY_LENGTH(referenced->parameters) !=
    ARRAY_LENGTH(thm_ref->children) - 1)
  {
    add_error(state->unit, data->location,
      "incorrect number of arguments supplied to theorem/axiom.");
    state->valid = FALSE;
  }
  Array args;
  ARRAY_INIT(args, struct Definition);
  for (size_t i = 0; i < ARRAY_LENGTH(referenced->parameters); ++i)
  {
    const struct ASTNode *arg =
      ARRAY_GET(thm_ref->children, struct ASTNode, i + 1);
    const struct ASTNodeData *arg_data = AST_NODE_DATA(arg);
    struct Value arg_value;
    int err = extract_value(state, arg, &arg_value, env);
    PROPAGATE_ERROR(err);

    const struct Parameter *param =
      ARRAY_GET(referenced->parameters, struct Parameter, i);
    if (!types_equal(arg_value.object_type, param->type))
    {
      add_error(state->unit, arg_data->location,
        "type of argument supplied to theorem/axiom is incorrect.");
      state->valid = FALSE;
    }

    struct Definition def;
    def.name = strdup(param->name);
    def.value = arg_value;
    ARRAY_APPEND(args, struct Definition, def);
  }
  int err = instantiate_theorem(state, referenced, args, env);
  PROPAGATE_ERROR(err);

  return 0;
}

static int
validate_theorem(struct ValidationState *state, const struct ASTNode *theorem)
{
  const struct ASTNodeData *data = AST_NODE_DATA(theorem);
  if (data->type != ASTNodeTypeTheorem)
  {
    add_error(state->unit, data->location,
      "expected an theorem statement but found the wrong type of node.");
    state->valid = FALSE;
  }

  struct Symbol sym = {};

  init_symbol_path(&sym.path);
  append_symbol_path(&sym.path, &state->prefix_path);

  struct SymbolPath local_path;
  init_symbol_path(&local_path);
  push_symbol_path(&local_path, data->name);
  append_symbol_path(&sym.path, &local_path);
  if (lookup_symbol(state, &local_path) != NULL)
  {
    add_error(state->unit, data->location,
      "theorem name already in use.");
    state->valid = FALSE;
  }
  free_symbol_path(&local_path);

  sym.type = SymbolTypeTheorem;

  struct Theorem *thm =
    malloc(sizeof(struct Theorem));
  thm->name = strdup(data->name);

  /* First, extract parameters. */
  ARRAY_INIT(thm->parameters, struct Parameter);
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(theorem->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeParameter)
    {
      int err = extract_parameter(state, child, &thm->parameters);
      PROPAGATE_ERROR(err);
    }
  }
  sym.object = thm;

  /* Then extract assumptions and inferences. */
  struct ProofEnvironment env;
  init_proof_environment(&env);
  for (size_t i = 0; i < ARRAY_LENGTH(thm->parameters); ++i)
  {
    const struct Parameter *param =
      ARRAY_GET(thm->parameters, struct Parameter, i);
    struct Parameter copy;
    copy_parameter(&copy, param);
    ARRAY_APPEND(env.parameters, struct Parameter, copy);
  }

  ARRAY_INIT(thm->assumptions, struct Value);
  ARRAY_INIT(thm->inferences, struct Value);
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
      int err = extract_assumption(state, child, thm, &env);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type == ASTNodeTypeInfer)
    {
      int err = extract_inference(state, child, thm, &env);
      PROPAGATE_ERROR(err);
    }
  }

  /* To validate the theorem, first add the assumptions to the environment as
     statements that have been proven, then go through the steps, adding the
     inferences of each to the list of proven statements. */
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(theorem->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeStep)
    {
      int err = validate_step(state, child, thm, &env);
      PROPAGATE_ERROR(err);
    }
  }

  /* Finally, make sure each inference claimed in the statement is proven. */
  for (size_t i = 0; i < ARRAY_LENGTH(thm->inferences); ++i)
  {
    const struct Value *inference =
      ARRAY_GET(thm->inferences, struct Value, i);
    if (!statement_proven(inference, &env))
    {
      add_error(state->unit, NULL,
        "inference not proven.");
      state->valid = FALSE;
    }
  }

  free_proof_environment(&env);
  ARRAY_APPEND(state->symbol_table, struct Symbol, sym);

  return 0;
}
#endif

struct ValidationState
{
  bool valid;
  FILE *out;

  struct CompilationUnit *unit;
  const struct ParserState *input;

  LogicState *logic;
  SymbolPath *prefix_path;
};

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

  SymbolPath *path = copy_symbol_path(state->prefix_path);
  push_symbol_path(path, data->typename);

  LogicError err = add_type(state->logic, path);
  if (err == LogicErrorSymbolAlreadyExists)
  {
    add_error(state->unit, data->location,
      "symbol already exists when declaring type.");
    state->valid = FALSE;
  }

  free_symbol_path(path);

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

  /*
  struct Symbol sym = {};

  init_symbol_path(&sym.path);
  append_symbol_path(&sym.path, &state->prefix_path);

  struct SymbolPath local_path;
  init_symbol_path(&local_path);
  push_symbol_path(&local_path, data->name);
  append_symbol_path(&sym.path, &local_path);
  if (lookup_symbol(state, &local_path) != NULL)
  {
    add_error(state->unit, data->location,
      "expression name already in use.");
    state->valid = FALSE;
  }
  free_symbol_path(&local_path);

  sym.type = SymbolTypeExpression;

  struct ObjectExpression *expr_object =
    malloc(sizeof(struct ObjectExpression));
  expr_object->name = strdup(data->name);

  struct SymbolPath type_path;
  init_symbol_path(&type_path);
  push_symbol_path(&type_path, data->typename);
  struct Symbol *type = lookup_symbol(state, &type_path);
  if (type == NULL)
  {
    add_error(state->unit, data->location,
      "unknown type of expression.");
    state->valid = FALSE;
  }
  if (type->type != SymbolTypeType)
  {
    add_error(state->unit, data->location,
      "Type provided as type of expression is not a type.");
    state->valid = FALSE;
  }
  expr_object->type = (struct ObjectType *)type->object;
  free_symbol_path(&type_path);

  ARRAY_INIT(expr_object->parameters, struct Parameter);
  for (size_t i = 0; i < ARRAY_LENGTH(expression->children); ++i)
  {
    const struct ASTNode *param =
      ARRAY_GET(expression->children, struct ASTNode, i);
    int err = extract_parameter(state, param, &expr_object->parameters);
    PROPAGATE_ERROR(err);
  }
  sym.object = expr_object;

  ARRAY_APPEND(state->symbol_table, struct Symbol, sym);*/

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

  /* Validate all the objects contained in this namespace. */
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
      case ASTNodeTypeType:
        err = validate_type(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeExpression:
        err = validate_expression(state, child);
        PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeAxiom:
        //err = validate_axiom(state, child);
        //PROPAGATE_ERROR(err);
        break;
      case ASTNodeTypeTheorem:
        //err = validate_theorem(state, child);
        //PROPAGATE_ERROR(err);
        break;
      default:
        add_error(state->unit, child_data->location,
          "expected a namespace, type, expression, axiom, or theorem, but found the wrong type of node.");
        state->valid = FALSE;
        break;
    }
  }

  if (data->name != NULL)
  {
    pop_symbol_path(state->prefix_path);
  }

  return 0;
}

static int
validate(struct ValidationState *state)
{
  state->logic = new_logic_state();
  state->prefix_path = init_symbol_path();

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
