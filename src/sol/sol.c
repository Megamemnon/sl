#include "sol.h"
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

const char *sol_keywords[] = {
  "namespace",
  "import",

  "judgement",
  "axiom",
  "theorem",

  "assume",
  "infer",
  "step",
  "def",
  NULL
};

const char *sol_symbols[] = {
  "(", ")",
  "[", "]",
  "{", "}",
  ".", ",", ";",
  "\\", "$", "=",
  "/*", "*/",
  "//",
  NULL
};

void
free_sol_node(struct ASTNode *node)
{
  struct SolASTNodeData *data = (struct SolASTNodeData *)node->data;

  if (data->name != NULL)
    free(data->name);

  free(data);
}

void
copy_sol_node(struct ASTNode *dst, const struct ASTNode *src)
{
  struct SolASTNodeData *dst_data = malloc(sizeof(struct SolASTNodeData));
  memset(dst_data, 0, sizeof(struct SolASTNodeData));

  const struct SolASTNodeData *src_data =
    (const struct SolASTNodeData *)src->data;
  dst_data->type = src_data->type;

  if (src_data->name != NULL)
    dst_data->name = strdup(src_data->name);
  else
    dst_data->name = NULL;

  dst->data = dst_data;
}

void
init_sol_node(struct ASTNode *node)
{
  struct SolASTNodeData *data = malloc(sizeof(struct SolASTNodeData));
  memset(data, 0, sizeof(struct SolASTNodeData));
  node->data = data;
  node->free_callback = &free_sol_node;
  node->copy_callback = &copy_sol_node;
}

struct SolASTNodeData *
get_sol_node_data(struct ASTNode *node)
{
  return (struct SolASTNodeData *)node->data;
}

const struct SolASTNodeData *
get_sol_node_data_c(const struct ASTNode *node)
{
  return (struct SolASTNodeData *)node->data;
}

/* Implementation of both `parse_program` and `parse_namespace`. */
static int
parse_namespace_interior(struct ParserState *state)
{
  int err = 0;
  while (state->token_index < ARRAY_LENGTH(*parser_token_buffer(state))
         && !consume_symbol(state, "}"))
  {
    if (consume_keyword(state, "namespace"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_namespace(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "import"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_import(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "judgement"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_judgement(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "axiom"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_axiom(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "theorem"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_theorem(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else
    {
      add_error(state->unit, get_current_token(state), "Unrecognized token.");
      return 1;
      break;
    }
  }
  return 0;
}

/* Called at the start of parsing. Almost equivalent to
   `parse_namespace`, except no curly braces. */
int
parse_program(struct ParserState *state)
{
  init_tree(&state->ast_root);

  init_sol_node(state->ast_current);
  get_sol_node_data(state->ast_current)->type = NodeTypeNamespace;
  return parse_namespace_interior(state);
}

/* A namespace, which is just a container for other objects. */
int
parse_namespace(struct ParserState *state)
{
  /* The next token should be an identifier giving the name of the namespace. */
  const char *namespace_name;
  if (!consume_identifier(state, &namespace_name))
  {
    add_error(state->unit, get_current_token(state),
      "No name provided for namespace.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeNamespace;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->name = strdup(namespace_name);

  /* Then there should be an opening bracket. */
  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected '{' following namespace name.");
    return 1;
  }

  int err = parse_namespace_interior(state);
  PROPAGATE_ERROR(err);

  return 0;
}

int
parse_import(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeImport;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* Iterate through the list of paths until we find a ';' */
  int first_path = 1;
  while (!consume_symbol(state, ";"))
  {
    /* Subsequent paths have commas. */
    if (!first_path && !consume_symbol(state, ","))
    {
      /* TODO: error: no separator. */
      add_error(state->unit, get_current_token(state),
        "No separator in path list.");
      return 1;
    }

    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    int err = parse_identifier_path(state);
    PROPAGATE_ERROR(err);
    ascend(state);

    if (first_path)
      first_path = 0;
  }

  return 0;
}

int
parse_judgement(struct ParserState *state)
{
  const char *judgement_name;
  if (!consume_identifier(state, &judgement_name))
  {
    add_error(state->unit, get_current_token(state),
      "No judgement name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeJudgement;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->name = strdup(judgement_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "No parameter list provided.");
    return 1;
  }
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_parameter_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Finally, expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected ';' after expression.");
    return 1;
  }

  return 0;
}

int
parse_axiom(struct ParserState *state)
{
  const char *axiom_name;
  if (!consume_identifier(state, &axiom_name))
  {
    add_error(state->unit, get_current_token(state),
      "Axioms must have a name.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeAxiom;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->name = strdup(axiom_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "Axioms must have a list of parameters.");
    return 1;
  }
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_parameter_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a definition inside curly brackets. */
  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "Axioms must have a definition");
    return 1;
  }

  while (state->token_index < ARRAY_LENGTH(*parser_token_buffer(state))
         && !consume_symbol(state, "}"))
  {
    if (consume_keyword(state, "assume"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_assume(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "infer"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_infer(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "def"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_def(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else
    {
      add_error(state->unit, get_current_token(state),
        "Unrecognized token.");
      return 1;
      break;
    }
  }
  return 0;
}

int
parse_theorem(struct ParserState *state)
{
  const char *theorem_name;
  if (!consume_identifier(state, &theorem_name))
  {
    add_error(state->unit, get_current_token(state),
      "No theorem name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeTheorem;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->name = strdup(theorem_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "No parameter list provided.");
    return 1;
  }
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_parameter_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a definition inside curly brackets. */
  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "Theorems must have a statement and proof.");
    return 1;
  }

  while (state->token_index < ARRAY_LENGTH(*parser_token_buffer(state))
         && !consume_symbol(state, "}"))
  {
    if (consume_keyword(state, "assume"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_assume(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "infer"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_infer(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "step"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_step(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else if (consume_keyword(state, "def"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_def(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else
    {
      add_error(state->unit, get_current_token(state),
        "Unrecognized token.");
      return 1;
      break;
    }
  }

  return 0;
}

int
parse_assume(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeAssume;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* There should be an expression for a judgement. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_judgement_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected ';' after assumption.");
    return 1;
  }
  return 0;
}

int
parse_infer(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeInfer;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* After the keyword, there should be a judgement expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_judgement_expression(state);
  PROPAGATE_ERROR(err);
  ascend(state);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected ';' after inferrence.");
    return 1;
  }
  return 0;
}

int
parse_step(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->type = NodeTypeStep;

  /* After the name, there should be an expression giving the inference. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_inference_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected ';' after proof step.");
    return 1;
  }

  return 0;
}

int
parse_def(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->type = NodeTypeDef;

  const char *def_name;
  if (!consume_identifier(state, &def_name))
  {
    add_error(state->unit, get_current_token(state),
      "No definition name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->name = strdup(def_name);

  /* After the name, there should be an expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected ';' after definition.");
    return 1;
  }

  return 0;
}

int
parse_judgement_expression(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeJudgementExpression;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* First, consume the path of the associated judgement. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_identifier_path(state);
  PROPAGATE_ERROR(err);
  ascend(state);

  /* Expect an opening '(' for the argument list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "No argument list provided in expression.");
    return 1;
  }

  /* Next, parse arguments. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  err = parse_argument_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  return 0;
}

int
parse_inference_expression(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeInferenceExpression;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* First, consume the path of the associated axiom/theorem. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_identifier_path(state);
  PROPAGATE_ERROR(err);
  ascend(state);

  /* Expect an opening '(' for the argument list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "No argument list provided in expression.");
    return 1;
  }

  /* Next, parse arguments. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  err = parse_argument_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  return 0;
}

int
parse_expression(struct ParserState *state)
{
  /* Expect a backslash to start the expression. */
  if (!consume_symbol(state, "\\"))
  {
    add_error(state->unit, get_current_token(state),
      "Expressions must start with '\\'.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->type = NodeTypeExpression;

  /* Loop through the expression until we find a terminating backslash. */
  while (!consume_symbol(state, "\\"))
  {
    if (consume_symbol(state, "$"))
    {
      /* If there is a '$' symbol, parse the variable expression. */
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      get_sol_node_data(state->ast_current)->type = NodeTypeExpressionVariable;
      get_sol_node_data(state->ast_current)->location = get_current_token(state);
      get_sol_node_data(state->ast_current)->name =
        strdup(get_current_token(state)->value);
      ascend(state);
      advance(state);
    }
    else if (consume_symbol(state, "%"))
    {
      /* If there is a '%' symbol, we have a placeholder (NOT a metavariable,
         just a C preprocessor-like subsitution). */
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      get_sol_node_data(state->ast_current)->type =
        NodeTypeExpressionPlaceholder;
      get_sol_node_data(state->ast_current)->location = get_current_token(state);
      get_sol_node_data(state->ast_current)->name =
        strdup(get_current_token(state)->value);
      ascend(state);
      advance(state);
    }
    else
    {
      /* Otherwise, just add the symbol as a "constant". */
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      get_sol_node_data(state->ast_current)->type = NodeTypeExpressionConstant;
      get_sol_node_data(state->ast_current)->location = get_current_token(state);
      get_sol_node_data(state->ast_current)->name =
        strdup(get_current_token(state)->value);
      ascend(state);
      advance(state);
    }
  }

  return 0;
}

int
parse_identifier_path(struct ParserState *state)
{
  /* We should always start with an identifier, and then alternate between dots
     and identifiers. */
  get_sol_node_data(state->ast_current)->type = NodeTypeIdentifierPath;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  const char *seg;
  if (!consume_identifier(state, &seg))
  {
    add_error(state->unit, get_current_token(state),
      "An identifier path needs at least one segment.");
    return 1;
  }

  /* TODO: should this be its own function? */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  get_sol_node_data(state->ast_current)->type = NodeTypeIdentifierPathSegment;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);
  get_sol_node_data(state->ast_current)->name = strdup(seg);
  ascend(state);

  while (consume_symbol(state, "."))
  {
    if (!consume_identifier(state, &seg))
    {
      add_error(state->unit, get_current_token(state),
        "All segments in an identifier path must be identifiers");
      return 1;
    }
    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    get_sol_node_data(state->ast_current)->type = NodeTypeIdentifierPathSegment;
    get_sol_node_data(state->ast_current)->location = get_current_token(state);
    get_sol_node_data(state->ast_current)->name = strdup(seg);
    ascend(state);
  }

  return 0;
}

int
parse_parameter_list(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeParameterList;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* Iterate through the list until we get a closing ')' */
  int first_param = 1;
  while (!consume_symbol(state, ")"))
  {
    /* Subsequent parameters have commas. */
    if (!first_param && !consume_symbol(state, ","))
    {
      add_error(state->unit, get_current_token(state),
        "Parameters must be comma-separated.");
      return 1;
    }

    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    get_sol_node_data(state->ast_current)->type = NodeTypeParameter;
    /* Parameters always have the form `[PARAM_NAME]`. */
    const char *parameter_name;
    if (!consume_identifier(state, &parameter_name))
    {
      add_error(state->unit, get_current_token(state),
        "No parameter name provided.");
      return 1;
    }
    get_sol_node_data(state->ast_current)->location = get_current_token(state);
    get_sol_node_data(state->ast_current)->name = strdup(parameter_name);
    ascend(state);

    if (first_param)
      first_param = 0;
  }

  /* Next, check for a definition. */
  return 0;
}

int
parse_argument_list(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeArgumentList;
  get_sol_node_data(state->ast_current)->location = get_current_token(state);

  /* Iterate through the list until we get a closing ')' */
  int first_arg = 1;
  while (!consume_symbol(state, ")"))
  {
    /* Subsequent parameters have commas. */
    if (!first_arg && !consume_symbol(state, ","))
    {
      add_error(state->unit, get_current_token(state),
        "Arguments must be comma-separated.");
      return 1;
    }

    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    int err = parse_expression(state);
    ascend(state);
    PROPAGATE_ERROR(err);

    if (first_arg)
      first_arg = 0;
  }

  /* Next, check for a definition. */
  return 0;
}

void
print_sol_node(char *buf, size_t len, const struct ASTNode *node)
{
  const struct SolASTNodeData *data = get_sol_node_data_c(node);
  const char *name = data->name;
  switch (get_sol_node_data_c(node)->type)
  {
    case NodeTypeNamespace:
      if (name == NULL)
        snprintf(buf, len, "Namespace<Unnamed>");
      else
        snprintf(buf, len, "Namespace<Name: \"%s\">", name);
      break;
    case NodeTypeImport:
      snprintf(buf, len, "Import");
      break;
    case NodeTypeJudgement:
      snprintf(buf, len, "Judgement<Name: \"%s\">", name);
      break;
    case NodeTypeAxiom:
      snprintf(buf, len, "Axiom<Name: \"%s\">", name);
      break;
    case NodeTypeTheorem:
      snprintf(buf, len, "Theorem<Name: \"%s\">", name);
      break;
    case NodeTypeAssume:
      snprintf(buf, len, "Assume");
      break;
    case NodeTypeInfer:
      snprintf(buf, len, "Infer");
      break;
    case NodeTypeStep:
      snprintf(buf, len, "Step");
      break;
    case NodeTypeDef:
      snprintf(buf, len, "Definition<Name: \"%s\">", name);
      break;
    case NodeTypeJudgementExpression:
      snprintf(buf, len, "Judgement Expression<Name: \"%s\">", name);
      break;
    case NodeTypeInferenceExpression:
      snprintf(buf, len, "Inference Expression<Name: \"%s\">", name);
      break;
    case NodeTypeExpression:
      snprintf(buf, len, "Expression");
      break;
    case NodeTypeExpressionConstant:
      snprintf(buf, len, "Constant<Name: \"%s\">", name);
      break;
    case NodeTypeExpressionVariable:
      snprintf(buf, len, "Variable<Name: \"%s\">", name);
      break;
    case NodeTypeIdentifierPath:
      snprintf(buf, len, "Path");
      break;
    case NodeTypeIdentifierPathSegment:
      snprintf(buf, len, "Path Segment<Identifier: \"%s\">", name);
      break;
    case NodeTypeParameterList:
      snprintf(buf, len, "Parameter List");
      break;
    case NodeTypeParameter:
      snprintf(buf, len, "Parameter<Name: \"%s\">", name);
      break;
    case NodeTypeArgumentList:
      snprintf(buf, len, "Argument List");
      break;
    default:
      snprintf(buf, len, "Unknown");
      break;
  }
}

int
copy_expression_symbol(struct ExpressionSymbol *dst,
  const struct ExpressionSymbol *src)
{
  dst->value = strdup(src->value);
  dst->type = src->type;
  return 0;
}

int
copy_expression(struct Expression *dst, const struct Expression *src)
{
  ARRAY_INIT(dst->symbols, struct ExpressionSymbol);
  for (size_t i = 0; i < ARRAY_LENGTH(src->symbols); ++i)
  {
    const struct ExpressionSymbol *src_symbol = ARRAY_GET(src->symbols,
      struct ExpressionSymbol, i);
    struct ExpressionSymbol dst_symbol = {};
    int err = copy_expression_symbol(&dst_symbol, src_symbol);
    PROPAGATE_ERROR(err);
    ARRAY_APPEND(dst->symbols, struct ExpressionSymbol, dst_symbol);
  }
  return 0;
}

void
free_expression_symbol(struct ExpressionSymbol *symbol)
{
  free(symbol->value);
}

void
free_expression(struct Expression *expression)
{
  for (size_t i = 0; i < ARRAY_LENGTH(expression->symbols); ++i)
  {
    struct ExpressionSymbol *sym = ARRAY_GET(expression->symbols,
      struct ExpressionSymbol, i);
    free_expression_symbol(sym);
  }
  ARRAY_FREE(expression->symbols);
}

char *
expression_to_string(const struct Expression *expr)
{
  size_t string_size = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(expr->symbols); ++i)
  {
    const struct ExpressionSymbol *sym = ARRAY_GET(expr->symbols,
      struct ExpressionSymbol, i);
    if (sym->type == ExpressionSymbolTypeConstant)
      string_size += strlen(sym->value) + 1;
    else
      string_size += strlen(sym->value) + 2;
  }

  char *str = malloc(string_size);
  char *c = str;
  for (size_t i = 0; i < ARRAY_LENGTH(expr->symbols); ++i)
  {
    const struct ExpressionSymbol *sym = ARRAY_GET(expr->symbols,
      struct ExpressionSymbol, i);
    if (sym->type == ExpressionSymbolTypeVariable)
    {
      *c = '$';
      ++c;
    }
    else if (sym->type == ExpressionSymbolTypePlaceholder)
    {
      *c = '%';
      ++c;
    }
    strcpy(c, sym->value);
    c[strlen(sym->value)] = ' ';
    c += strlen(sym->value) + 1;
  }
  str[string_size - 1] = '\0';

  return str;
}

void
free_scope_node(struct ASTNode *node)
{
  struct SolScopeNodeData *data = (struct SolScopeNodeData *)node->data;

  if (data->name != NULL)
    free(data->name);

  for (size_t i = 0; i < ARRAY_LENGTH(data->symbol_table); ++i)
  {
    struct Symbol *sym = ARRAY_GET(data->symbol_table, struct Symbol, i);
    free(sym->name);

    struct SolObject *obj = sym->object;

    for (size_t j = 0; j < ARRAY_LENGTH(obj->parameters); ++j)
    {
      char **param = ARRAY_GET(obj->parameters, char *, j);
      free(*param);
    }
    ARRAY_FREE(obj->parameters);

    for (size_t j = 0; j < ARRAY_LENGTH(obj->assumptions); ++j)
    {
      struct JudgementInstance *assume = ARRAY_GET(obj->assumptions,
        struct JudgementInstance, j);
      for (size_t k = 0; k < ARRAY_LENGTH(assume->expression_args); ++k)
      {
        struct Expression *expr = ARRAY_GET(assume->expression_args,
          struct Expression, k);
        free_expression(expr);
      }
      ARRAY_FREE(assume->expression_args);
    }
    ARRAY_FREE(obj->assumptions);

    for (size_t j = 0; j < ARRAY_LENGTH(obj->inferences); ++j)
    {
      struct JudgementInstance *infer = ARRAY_GET(obj->inferences,
        struct JudgementInstance, j);
      for (size_t k = 0; k < ARRAY_LENGTH(infer->expression_args); ++k)
      {
        struct Expression *expr = ARRAY_GET(infer->expression_args,
          struct Expression, k);
        free_expression(expr);
      }
      ARRAY_FREE(infer->expression_args);
    }
    ARRAY_FREE(obj->inferences);

    free(obj);
  }

  ARRAY_FREE(data->symbol_table);
  ARRAY_FREE(data->symbol_search_locations);

  free(data);
}

void
copy_scope_node(struct ASTNode *dst, const struct ASTNode *src)
{

}

void
init_scope_node(struct ASTNode *node)
{
  struct SolScopeNodeData *data = malloc(sizeof(struct SolScopeNodeData));
  memset(data, 0, sizeof(struct SolScopeNodeData));
  node->data = data;
  node->free_callback = &free_scope_node;
  node->copy_callback = &copy_scope_node;
}

static struct SolObject *
lookup_in_scope(struct ASTNode *scope, const struct ObjectName *path)
{
  struct ASTNode *namespace = scope;
  for (size_t i = 0; i < ARRAY_LENGTH(path->segments); ++i)
  {
    const char *segment = *ARRAY_GET(path->segments, char *, i);
    /* The last segment is the name of the object in its parent namespace.
       The preceding segments are nested namespace names. */
    if (i == ARRAY_LENGTH(path->segments) - 1)
    {
      /* Look for the symbol in this namespace. */
      struct SolScopeNodeData *data = get_scope_node_data(namespace);
      for (size_t j = 0; j < ARRAY_LENGTH(data->symbol_table); ++j)
      {
        struct Symbol *symbol = ARRAY_GET(data->symbol_table, struct Symbol, j);
        if (strcmp(symbol->name, segment) == 0)
          return symbol->object;
      }
      /* If we can't find it here, it doesn't exist. */
      return NULL;
    }
    else
    {
      /* Find the child namespace. */
      for (size_t j = 0; j < ARRAY_LENGTH(namespace->children); ++j)
      {
        struct ASTNode *child = ARRAY_GET(namespace->children,
          struct ASTNode, j);
        struct SolScopeNodeData *child_data = get_scope_node_data(child);
        if (strcmp(child_data->name, segment) == 0)
        {
          namespace = child;
          break;
        }
      }
      /* No such object if we can't find the namespace. */
      return NULL;
    }
  }
  return NULL;
}

struct SolObject *
lookup_symbol(struct ASTNode *scope, const struct ObjectName *path)
{
  /* First, iterate through the list of parents of this scope to check for
     the symbol. If we don't find anything, check through the extra search
     locations. */
  struct SolScopeNodeData *scope_data = get_scope_node_data(scope);
  struct ASTNode *searching_in = scope;
  struct SolObject *obj = NULL;
  do
  {
    obj = lookup_in_scope(searching_in, path);
    if (obj != NULL)
      return obj;
    searching_in = searching_in->parent;
  }
  while (searching_in != NULL);

  for (size_t i = 0; i < ARRAY_LENGTH(scope_data->symbol_search_locations);
       ++i)
  {
    searching_in = *ARRAY_GET(scope_data->symbol_search_locations,
      struct ASTNode *, i);
    obj = lookup_in_scope(searching_in, path);
    if (obj != NULL)
      return obj;
  }

  return NULL;
}

struct SolScopeNodeData *
get_scope_node_data(struct ASTNode *node)
{
  return (struct SolScopeNodeData *)node->data;
}

const struct SolScopeNodeData *
get_scope_node_data_c(const struct ASTNode *node)
{
  return (struct SolScopeNodeData *)node->data;
}

char *
judgement_instance_to_string(const struct JudgementInstance *inst)
{
  size_t string_size = /*strlen(inst->judgement) + */1;

  Array expressions;
  ARRAY_INIT(expressions, char *);
  for (size_t i = 0; i < ARRAY_LENGTH(inst->expression_args); ++i)
  {
    const struct Expression *expr = ARRAY_GET(inst->expression_args,
      struct Expression, i);
    char *expr_str = expression_to_string(expr);
    ARRAY_APPEND(expressions, char *, expr_str);
    string_size += strlen(expr_str) + 2;
  }

  char *str = malloc(string_size);
  char *c = str;
  c[0] = '(';
  c += 1;
  /*strcpy(c, inst->judgement);
  c[strlen(inst->judgement)] = '(';
  c += strlen(inst->judgement) + 1;*/
  for (size_t i = 0; i < ARRAY_LENGTH(inst->expression_args); ++i)
  {
    const struct Expression *expr = ARRAY_GET(inst->expression_args,
      struct Expression, i);
    char *expr_str = expression_to_string(expr);
    strcpy(c, expr_str);
    if (i == ARRAY_LENGTH(inst->expression_args) - 1)
    {
      c[strlen(expr_str)] = ')';
      c[strlen(expr_str) + 1] = '\0';
    }
    else
    {
      c[strlen(expr_str)] = ',';
      c[strlen(expr_str) + 1] = ' ';
      c += strlen(expr_str) + 2;
    }
  }
  return str;
}

void
free_name(struct ObjectName *path)
{
  for (size_t i = 0; i < ARRAY_LENGTH(path->segments); ++i)
  {
    char *segment = *ARRAY_GET(path->segments, char *, i);
    free(segment);
  }
  ARRAY_FREE(path->segments);
}

int
extract_path(struct ObjectName *path, const struct ASTNode *identifier_path)
{
  ARRAY_INIT(path->segments, char *);

  const struct SolASTNodeData *identifier_path_data =
    get_sol_node_data_c(identifier_path);
  if (identifier_path_data->type != NodeTypeIdentifierPath)
  {
    /* TODO: error detail. */
    return 1;
  }

  /* Loop through the children. */
  for (size_t i = 0; i < ARRAY_LENGTH(identifier_path->children); ++i)
  {
    const struct ASTNode *segment = ARRAY_GET(identifier_path->children,
      struct ASTNode, i);
    const struct SolASTNodeData *segment_data = get_sol_node_data_c(segment);
    if (segment_data->type != NodeTypeIdentifierPathSegment)
      return 1;
    ARRAY_APPEND(path->segments, char *, strdup(segment_data->name));
  }

  return 0;
}

char *
name_to_string(const struct ObjectName *name)
{
  size_t total_length = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(name->segments); ++i)
  {
    const char *segment = *ARRAY_GET(name->segments, char *, i);
    total_length += strlen(segment);
  }

  /* Add in room for the delimiting dots. */
  total_length += ARRAY_LENGTH(name->segments) - 1;

  char *buf = malloc(sizeof(char) * (total_length + 1));

  char *current = buf;
  int first_segment = 1;
  for (size_t i = 0; i < ARRAY_LENGTH(name->segments); ++i)
  {
    if (!first_segment)
    {
      /* Add the preceding dot. */
      *current = '.';
      ++current;
    }

    const char *segment = *ARRAY_GET(name->segments, char *, i);
    strncpy(current, segment, strlen(segment));
    current += strlen(segment);

    if (first_segment)
      first_segment = 0;
  }

  buf[total_length] = '\0';

  return buf;
}

int
validate_expression(struct ValidationState *state,
  struct Expression *dst,
  const struct ASTNode *ast_expression,
  const struct SolObject *env,
  int depth)
{
  ARRAY_INIT(dst->symbols, struct ExpressionSymbol);

  /* Loop through the children in the AST. */
  for (size_t i = 0; i < ARRAY_LENGTH(ast_expression->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_expression->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);
    if (child_data->type == NodeTypeExpressionConstant)
    {
      struct ExpressionSymbol sym = {};
      sym.value = strdup(child_data->name);
      sym.type = ExpressionSymbolTypeConstant;
      ARRAY_APPEND(dst->symbols, struct ExpressionSymbol, sym);
    }
    else if (child_data->type == NodeTypeExpressionVariable)
    {
      /* The variable must be a parameter of the environment. */
      int var_index = -1;
      for (size_t j = 0; j < ARRAY_LENGTH(env->parameters); ++j)
      {
        const struct Parameter *param =
          ARRAY_GET(env->parameters, struct Parameter, j);
        if (strcmp(child_data->name, param->name) == 0)
        {
          var_index = j;
          break;
        }
      }

      if (var_index == -1)
      {
        add_error(state->unit, child_data->location,
          "variable is not declared as a parameter of this object");
        /* TODO: free. */
        return 1;
      }

      struct ExpressionSymbol sym;
      sym.value = strdup(child_data->name);
      sym.type = ExpressionSymbolTypeVariable;

      ARRAY_APPEND(dst->symbols, struct ExpressionSymbol, sym);
    }
    else if (child_data->type == NodeTypeExpressionPlaceholder)
    {
      /* TODO: Find the definition of this symbol. */
      struct ExpressionSymbol sym;
      sym.value = strdup(child_data->name);
      sym.type = ExpressionSymbolTypePlaceholder;

      ARRAY_APPEND(dst->symbols, struct ExpressionSymbol, sym);
    }
    else
    {
      /* TODO: Error, and free. */
      add_error(state->unit, child_data->location,
        "incorrect node type.");
      return 1;
    }
  }

  return 0;
}

int
validate_assume(struct ValidationState *state,
  const struct ASTNode *ast_assume,
  struct SolObject *env)
{
  struct JudgementInstance assume;

  /* TODO: Lookup the relevant judgement. */
  {
    const struct SolASTNodeData *assume_data = get_sol_node_data_c(ast_assume);
    assume.location = assume_data->location;
  }

  const struct ASTNode *ast_je = ARRAY_GET(ast_assume->children,
    struct ASTNode, 0);
  const struct SolASTNodeData *je_data =
    get_sol_node_data_c(ast_je);
  if (je_data->type != NodeTypeJudgementExpression)
  {
    /* TODO: error detail. */
    add_error(state->unit, je_data->location,
      "incorrect node type.");
    return 1;
  }
  if (ARRAY_LENGTH(ast_je->children) != 2)
  {
    add_error(state->unit, je_data->location,
      "judgement expressions should have two children.");
    return 1;
  }

  /* First, there should be a child containing the path to the referenced
     judgement. */
  {
    const struct ASTNode *ast_path = ARRAY_GET(ast_je->children,
      struct ASTNode, 0);
    const struct SolASTNodeData *ast_path_data =
      get_sol_node_data_c(ast_path);
    struct ObjectName path = {};
    int err = extract_path(&path, ast_path);
    if (err)
    {
      /* TODO: error. */
      add_error(state->unit, ast_path_data->location,
        "error extracting object path.");
      return 1;
    }
    assume.judgement = lookup_symbol(state->scope_current, &path);
    /* TODO: this should be its own utility function. */
    free_name(&path);
    if (assume.judgement == NULL)
    {
      /* TODO: error. */
      add_error(state->unit, ast_path_data->location,
        "unknown judgement.");
      return 1;
    }
  }

  const struct ASTNode *ast_args = ARRAY_GET(ast_je->children,
    struct ASTNode, 1);
  const struct SolASTNodeData *args_data =
    get_sol_node_data_c(ast_args);
  if (args_data->type != NodeTypeArgumentList)
  {
    /* TODO: error. */
    add_error(state->unit, args_data->location,
      "incorrect node type.");
    return 1;
  }

  /* TODO: Verify that the correct number of arguments are supplied. */
  ARRAY_INIT(assume.expression_args, struct Expression);
  for (size_t i = 0; i < ARRAY_LENGTH(ast_args->children); ++i)
  {
    const struct ASTNode *ast_arg = ARRAY_GET(ast_args->children,
      struct ASTNode, i);
    const struct SolASTNodeData *arg_data =
      get_sol_node_data_c(ast_arg);
    struct Expression expr = {};
    int err = validate_expression(state, &expr, ast_arg, env, 0);
    PROPAGATE_ERROR(err);
    ARRAY_APPEND(assume.expression_args, struct Expression, expr);
  }

  ARRAY_APPEND(env->assumptions, struct JudgementInstance, assume);

  return 0;
}

int
validate_infer(struct ValidationState *state,
  const struct ASTNode *ast_infer,
  struct SolObject *env)
{
  struct JudgementInstance infer;

  {
    const struct SolASTNodeData *infer_data = get_sol_node_data_c(ast_infer);
    infer.location = infer_data->location;
  }

  /* TODO: Lookup the relevant judgement. */

  const struct ASTNode *ast_je = ARRAY_GET(ast_infer->children,
    struct ASTNode, 0);
  const struct SolASTNodeData *je_data =
    get_sol_node_data_c(ast_je);
  if (je_data->type != NodeTypeJudgementExpression)
  {
    /* TODO: error detail. */
    add_error(state->unit, je_data->location,
      "incorrect node type.");
    return 1;
  }
  if (ARRAY_LENGTH(ast_je->children) != 2)
  {
    add_error(state->unit, je_data->location,
      "judgement expressions should have two children.");
    return 1;
  }

  /* First, there should be a child containing the path to the referenced
     judgement. */
  {
    const struct ASTNode *ast_path = ARRAY_GET(ast_je->children,
      struct ASTNode, 0);
    const struct SolASTNodeData *ast_path_data =
      get_sol_node_data_c(ast_path);
    struct ObjectName path = {};
    int err = extract_path(&path, ast_path);
    if (err)
    {
      /* TODO: error. */
      add_error(state->unit, ast_path_data->location,
        "error extracting object path.");
      return 1;
    }
    infer.judgement = lookup_symbol(state->scope_current, &path);
    /* TODO: this should be its own utility function. */
    free_name(&path);
    if (infer.judgement == NULL)
    {
      /* TODO: error. */
      add_error(state->unit, ast_path_data->location,
        "unknown judgement.");
      return 1;
    }
  }

  const struct ASTNode *ast_args = ARRAY_GET(ast_je->children,
    struct ASTNode, 1);
  const struct SolASTNodeData *args_data =
    get_sol_node_data_c(ast_args);
  if (args_data->type != NodeTypeArgumentList)
  {
    /* TODO: error. */
    add_error(state->unit, args_data->location,
      "incorrect node type.");
    return 1;
  }

  /* TODO: Verify that the correct number of arguments are supplied. */
  ARRAY_INIT(infer.expression_args, struct Expression);
  for (size_t i = 0; i < ARRAY_LENGTH(ast_args->children); ++i)
  {
    const struct ASTNode *ast_arg = ARRAY_GET(ast_args->children,
      struct ASTNode, i);
    const struct SolASTNodeData *arg_data =
      get_sol_node_data_c(ast_arg);
    struct Expression expr = {};
    int err = validate_expression(state, &expr, ast_arg, env, 0);
    PROPAGATE_ERROR(err);
    ARRAY_APPEND(infer.expression_args, struct Expression, expr);
  }

  ARRAY_APPEND(env->inferences, struct JudgementInstance, infer);

  return 0;
}

int
validate_import(struct ValidationState *state,
  const struct ASTNode *ast_import)
{
  /* Add the import path to the list of search paths. */
  struct ASTNode *scope_node = state->scope_current;
  struct SolScopeNodeData *scope_data = get_scope_node_data(scope_node);

  /* The first child should be an NodeTypeIdentifierPath. Assemble
     the path from its children. */
  for (size_t i = 0; i < ARRAY_LENGTH(ast_import->children); ++i)
  {
    const struct ASTNode *ast_path = ARRAY_GET(ast_import->children,
      struct ASTNode, i);
    const struct SolASTNodeData *path_data = get_sol_node_data_c(ast_path);
    if (path_data->type != NodeTypeIdentifierPath)
    {
      /* TODO: error. */
      add_error(state->unit, path_data->location,
        "incorrect node type.");
      return 1;
    }

    /* Locate the scope that is being pointed to. */
    struct ASTNode *import_scope = &state->scope_tree_root;
    for (size_t i = 0; i < ARRAY_LENGTH(ast_path->children); ++i)
    {
      const struct ASTNode *child = ARRAY_GET(ast_path->children,
        struct ASTNode, 0);
      const struct SolASTNodeData *child_data = get_sol_node_data_c(child);

      if (child_data->type != NodeTypeIdentifierPathSegment)
      {
        /* TODO: error. */
        add_error(state->unit, child_data->location,
          "incorrect node type.");
        return 1;
      }

      /* Find the child. */
      bool found_child = FALSE;
      for (size_t j = 0; j < ARRAY_LENGTH(import_scope->children); ++j)
      {
        struct ASTNode *scope_child = ARRAY_GET(import_scope->children,
          struct ASTNode, j);
        struct SolScopeNodeData *scope_data = get_scope_node_data(scope_child);
        if (strcmp(scope_data->name, child_data->name) == 0)
        {
          import_scope = scope_child;
          found_child = TRUE;
          break;
        }
      }
      if (!found_child)
      {
        add_error(state->unit, child_data->location,
          "cannot locate namespace.");
        return 1;
      }
    }

    /* TODO: verify that importing it does not introduce collisions. */
    /* To verify that no name collisions are introduced, try to add each
       object as an element of this namespace. */

    ARRAY_APPEND(scope_data->symbol_search_locations, struct ASTNode *,
      import_scope);
  }

  return 0;
}

int
validate_judgement(struct ValidationState *state,
  const struct ASTNode *ast_judgement)
{
  struct SolObject *judgement = malloc(sizeof(struct SolObject));
  memset(judgement, 0, sizeof(struct SolObject));
  judgement->type = SolObjectTypeJudgement;

  struct ASTNode *scope_node = state->scope_current;
  struct SolScopeNodeData *scope_data = get_scope_node_data(scope_node);

  /* The first child should be an NodeTypeParameterList. */
  const struct ASTNode *ast_plist = ARRAY_GET(ast_judgement->children,
    struct ASTNode, 0);
  const struct SolASTNodeData *plist_data = get_sol_node_data_c(ast_plist);
  if (plist_data->type != NodeTypeParameterList)
  {
    /* TODO: error. */
    add_error(state->unit, plist_data->location,
      "incorrect node type.");
    return 1;
  }

  ARRAY_INIT(judgement->parameters, struct Parameter);

  for (size_t i = 0; i < ARRAY_LENGTH(ast_plist->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_plist->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);

    if (child_data->type != NodeTypeParameter)
    {
      /* TODO: error. */
      add_error(state->unit, child_data->location,
        "incorrect node type.");
      return 1;
    }

    struct Parameter param;
    param.name = strdup(child_data->name);

    ARRAY_APPEND(judgement->parameters, struct Parameter, param);
  }

  /* TODO: verify that adding this will not introduce any collisions. */
  struct Symbol symbol = {
    .name = strdup(get_sol_node_data_c(ast_judgement)->name),
    .object = judgement
  };
  ARRAY_APPEND(scope_data->symbol_table, struct Symbol, symbol);

  return 0;
}

int
validate_axiom(struct ValidationState *state,
  const struct ASTNode *ast_axiom)
{
  struct SolObject *axiom = malloc(sizeof(struct SolObject));
  memset(axiom, 0, sizeof(struct SolObject));
  axiom->type = SolObjectTypeTheorem;

  struct ASTNode *scope_node = state->scope_current;
  struct SolScopeNodeData *scope_data = get_scope_node_data(scope_node);

  /* The first child should be a NodeTypeParameterList. */
  const struct ASTNode *ast_plist = ARRAY_GET(ast_axiom->children,
    struct ASTNode, 0);
  const struct SolASTNodeData *plist_data = get_sol_node_data_c(ast_plist);
  if (plist_data->type != NodeTypeParameterList)
  {
    /* TODO: error. */
    add_error(state->unit, plist_data->location,
      "incorrect node type.");
    return 1;
  }

  ARRAY_INIT(axiom->parameters, struct Parameter);

  for (size_t i = 0; i < ARRAY_LENGTH(ast_plist->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_plist->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);

    if (child_data->type != NodeTypeParameter)
    {
      /* TODO: error. */
      add_error(state->unit, child_data->location,
        "incorrect node type.");
      return 1;
    }

    struct Parameter param;
    param.name = strdup(child_data->name);

    ARRAY_APPEND(axiom->parameters, struct Parameter, param);
  }

  /* Next, scan for assumptions and inferences. */
  ARRAY_INIT(axiom->assumptions, struct JudgementInstance);
  ARRAY_INIT(axiom->inferences, struct JudgementInstance);
  for (size_t i = 0; i < ARRAY_LENGTH(ast_axiom->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_axiom->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);
    if (child_data->type == NodeTypeAssume)
    {
      int err = validate_assume(state, child, axiom);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type == NodeTypeInfer)
    {
      int err = validate_infer(state, child, axiom);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type != NodeTypeParameterList)
    {
      /* TODO: error. */
      add_error(state->unit, child_data->location,
        "incorrect node type.");
      return 1;
    }
  }

  /* TODO: verify that adding this will not introduce any collisions. */
  struct Symbol symbol = {
    .name = strdup(get_sol_node_data_c(ast_axiom)->name),
    .object = axiom
  };
  ARRAY_APPEND(scope_data->symbol_table, struct Symbol, symbol);
  return 0;
}

int
substitute_into_expression(struct ValidationState *state,
  struct Expression *dst, const struct Expression *expr,
  const struct ArgumentList *args)
{
  ARRAY_INIT(dst->symbols, struct ExpressionSymbol);

  Array component_expressions;
  ARRAY_INIT(component_expressions, struct Expression);
  /* Loop through the symbols in `expr`. Create a new expression corresponding
     to each symbol. */
  for (size_t i = 0; i < ARRAY_LENGTH(expr->symbols); ++i)
  {
    const struct ExpressionSymbol *s = ARRAY_GET(expr->symbols,
      struct ExpressionSymbol, i);

    struct Expression component = {};
    ARRAY_INIT(component.symbols, struct ExpressionSymbol);
    if (s->type == ExpressionSymbolTypeVariable)
    {
      Array component_expressions;
      ARRAY_INIT(component_expressions, struct Expression);

      const struct Expression *src = NULL;
      for (size_t j = 0; j < ARRAY_LENGTH(args->arguments); ++j)
      {
        const struct Argument *argument = ARRAY_GET(args->arguments,
          struct Argument, j);
        if (strcmp(s->value, argument->name) == 0)
        {
          src = &argument->value;
          break;
        }
      }

      if (src == NULL)
      {
        /* TODO: error. */
        add_error(state->unit, NULL,
          "error performing replacement.");
        return 1;
      }

      copy_expression(&component, src);
    }
    else
    {
      /* Just copy the constant into its own expression. */
      struct ExpressionSymbol symbol = {};
      int err = copy_expression_symbol(&symbol, s);
      if (err)
      {
        add_error(state->unit, NULL,
          "error copying symbol.");
        return 1;
      }
      ARRAY_APPEND(component.symbols, struct ExpressionSymbol, symbol);
    }
    ARRAY_APPEND(component_expressions, struct Expression, component);
  }

  /* Join all the expressions together. */
  for (size_t i = 0; i < ARRAY_LENGTH(component_expressions); ++i)
  {
    struct Expression *component = ARRAY_GET(component_expressions,
      struct Expression, i);
    for (size_t j = 0; j < ARRAY_LENGTH(component->symbols); ++j)
    {
      const struct ExpressionSymbol *src_symbol = ARRAY_GET(component->symbols,
        struct ExpressionSymbol, j);
      struct ExpressionSymbol symbol = {};
      int err = copy_expression_symbol(&symbol, src_symbol);
      if (err)
      {
        add_error(state->unit, NULL,
          "error joining expressions.");
        return 1;
      }
      ARRAY_APPEND(dst->symbols, struct ExpressionSymbol, symbol);
    }
    /* TODO: free `component`. */
    free_expression(component);
  }

  ARRAY_FREE(component_expressions);

  return 0;
}

bool
symbols_equal(const struct ExpressionSymbol *a,
  const struct ExpressionSymbol *b)
{
  if (strcmp(a->value, b->value) != 0)
    return FALSE;
  if (a->type != b->type)
    return FALSE;
  return TRUE;
}

bool
expressions_equal(const struct Expression *a, const struct Expression *b)
{
  if (ARRAY_LENGTH(a->symbols) != ARRAY_LENGTH(b->symbols))
    return FALSE;
  for (size_t i = 0; i < ARRAY_LENGTH(a->symbols); ++i)
  {
    const struct ExpressionSymbol *sym_a = ARRAY_GET(a->symbols,
      struct ExpressionSymbol, i);
    const struct ExpressionSymbol *sym_b = ARRAY_GET(b->symbols,
      struct ExpressionSymbol, i);
    if (!symbols_equal(sym_a, sym_b))
      return FALSE;
  }
  return TRUE;
}

int
instantiate_object(struct ValidationState *state, const struct SolObject *obj,
  const struct ArgumentList *args, struct ProofEnv *env)
{
  /* First, perform substitutions to obtain the instantiated form of all the
     assumptions and inferences. */
  Array assumptions;
  ARRAY_INIT(assumptions, struct JudgementInstance);
  for (size_t i = 0; i < ARRAY_LENGTH(obj->assumptions); ++i)
  {
    const struct JudgementInstance *assume_pre = ARRAY_GET(obj->assumptions,
      struct JudgementInstance, i);
    struct JudgementInstance assume = {};
    assume.judgement = assume_pre->judgement;
    assume.location = assume_pre->location;
    ARRAY_INIT(assume.expression_args, struct Expression);
    for (size_t j = 0; j < ARRAY_LENGTH(assume_pre->expression_args); ++j)
    {
      const struct Expression *expr_pre = ARRAY_GET(assume_pre->expression_args,
        struct Expression, j);
      struct Expression expr = {};
      substitute_into_expression(state, &expr, expr_pre, args);
      ARRAY_APPEND(assume.expression_args, struct Expression, expr);
    }
    ARRAY_APPEND(assumptions, struct JudgementInstance, assume);
  }

  /* Check that each instantiated assumption is in the environment. */
  for (size_t i = 0; i < ARRAY_LENGTH(assumptions); ++i)
  {
    struct JudgementInstance *assume = ARRAY_GET(assumptions,
      struct JudgementInstance, i);
    if (!judgement_proved(state, env, assume))
    {
      /* TODO: error. */
      add_error(state->unit, assume->location,
        "assumption not met during instantiation.");
      return 1;
    }
    for (size_t j = 0; j < ARRAY_LENGTH(assume->expression_args); ++j)
    {
      struct Expression *expr = ARRAY_GET(assume->expression_args,
        struct Expression, j);
      free_expression(expr);
    }
    ARRAY_FREE(assume->expression_args);
  }

  ARRAY_FREE(assumptions);

  /* The assumptions hold, so we are free to add the instantiated inferences to
     our proof environment. */
  for (size_t i = 0; i < ARRAY_LENGTH(obj->inferences); ++i)
  {
    const struct JudgementInstance *infer_pre = ARRAY_GET(obj->inferences,
      struct JudgementInstance, i);
    struct JudgementInstance infer = {};
    infer.judgement = infer_pre->judgement;
    ARRAY_INIT(infer.expression_args, struct Expression);
    for (size_t j = 0; j < ARRAY_LENGTH(infer_pre->expression_args); ++j)
    {
      const struct Expression *expr_pre = ARRAY_GET(infer_pre->expression_args,
        struct Expression, j);
      struct Expression expr = {};
      substitute_into_expression(state, &expr, expr_pre, args);
      ARRAY_APPEND(infer.expression_args, struct Expression, expr);
    }
    char *str = judgement_instance_to_string(&infer);
    ARRAY_APPEND(env->proven, struct JudgementInstance, infer);
  }

  return 0;
}

bool
judgement_proved(struct ValidationState *state, const struct ProofEnv *env,
  const struct JudgementInstance *judgement)
{
  /* First, check for builtins, which should be treated as special cases. */
#if 0
  if (strcmp(judgement->judgement, "distinct") == 0)
  {
    /* In this case, we should have two arguments. Check for equality
       of expressions. */
    if (ARRAY_LENGTH(judgement->expression_args) != 2)
    {
      /* TODO: error. */
      return 1;
    }
    const struct Expression *a = ARRAY_GET(judgement->expression_args,
      struct Expression, 0);
    const struct Expression *b = ARRAY_GET(judgement->expression_args,
      struct Expression, 1);
    if (expressions_equal(a, b))
    {
      /* TODO: error. */
      return 1;
    }
    else
    {
      return 0;
    }
  }
#endif

  /* Loop through the judgements that we have proven, and check for equality
     by comparing names and the arguments passed. */
  for (size_t i = 0; i < ARRAY_LENGTH(env->proven); ++i)
  {
    const struct JudgementInstance *proven = ARRAY_GET(env->proven,
      struct JudgementInstance, i);

    if (proven->judgement != judgement->judgement)
      continue;
    if (ARRAY_LENGTH(proven->expression_args)
        != ARRAY_LENGTH(judgement->expression_args))
      continue;
    bool args_equal = TRUE;
    for (size_t j = 0; j < ARRAY_LENGTH(proven->expression_args); ++j)
    {
      const struct Expression *proven_arg = ARRAY_GET(proven->expression_args,
        struct Expression, j);
      const struct Expression *checking_arg =
        ARRAY_GET(judgement->expression_args, struct Expression, j);
      if (!expressions_equal(proven_arg, checking_arg))
      {
        args_equal = FALSE;
        break;
      }
    }
    if (args_equal)
      return TRUE;
  }
  return FALSE;
}

int
validate_theorem(struct ValidationState *state,
  const struct ASTNode *ast_theorem)
{
  struct SolObject *theorem = malloc(sizeof(struct SolObject));
  memset(theorem, 0, sizeof(struct SolObject));
  theorem->type = SolObjectTypeTheorem;

  struct ASTNode *scope_node = state->scope_current;
  struct SolScopeNodeData *scope_data = get_scope_node_data(scope_node);

  /* The first child should be a NodeTypeParameterList. */
  const struct ASTNode *ast_plist = ARRAY_GET(ast_theorem->children,
    struct ASTNode, 0);
  const struct SolASTNodeData *plist_data = get_sol_node_data_c(ast_plist);
  if (plist_data->type != NodeTypeParameterList)
  {
    /* TODO: error. */
    add_error(state->unit, plist_data->location,
      "incorrect node type.");
    return 1;
  }

  ARRAY_INIT(theorem->parameters, struct Parameter);
  for (size_t i = 0; i < ARRAY_LENGTH(ast_plist->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_plist->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);

    if (child_data->type != NodeTypeParameter)
    {
      /* TODO: error. */
      add_error(state->unit, child_data->location,
        "incorrect node type.");
      return 1;
    }

    struct Parameter param;
    param.name = strdup(child_data->name);

    ARRAY_APPEND(theorem->parameters, struct Parameter, param);
  }

  /* Next, scan for assumptions and inferences. */
  ARRAY_INIT(theorem->assumptions, struct JudgementInstance);
  ARRAY_INIT(theorem->inferences, struct JudgementInstance);
  for (size_t i = 0; i < ARRAY_LENGTH(ast_theorem->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_theorem->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);
    if (child_data->type == NodeTypeAssume)
    {
      int err = validate_assume(state, child, theorem);
      PROPAGATE_ERROR(err);
    }
    else if (child_data->type == NodeTypeInfer)
    {
      int err = validate_infer(state, child, theorem);
      PROPAGATE_ERROR(err);
    }
  }

  /* Set up the proof environment and add in the assumptions
     we started with. */
  struct ProofEnv env = {};
  ARRAY_INIT(env.proven, struct JudgementInstance);

  for (size_t i = 0; i < ARRAY_LENGTH(theorem->assumptions); ++i)
  {
    const struct JudgementInstance *assume = ARRAY_GET(theorem->assumptions,
      struct JudgementInstance, i);

    struct JudgementInstance proven = {};
    proven.judgement = assume->judgement;
    ARRAY_INIT(proven.expression_args, struct Expression);
    for (size_t j = 0; j < ARRAY_LENGTH(assume->expression_args); ++j)
    {
      const struct Expression *arg = ARRAY_GET(assume->expression_args,
        struct Expression, j);
      struct Expression copied_arg;
      copy_expression(&copied_arg, arg);
      ARRAY_APPEND(proven.expression_args, struct Expression,
        copied_arg);
    }
    ARRAY_APPEND(env.proven, struct JudgementInstance, proven);
  }

  /* Verify the validity of each proof step. */
  for (size_t i = 0; i < ARRAY_LENGTH(ast_theorem->children); ++i)
  {
    const struct ASTNode *child = ARRAY_GET(ast_theorem->children,
      struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);
    if (child_data->type == NodeTypeStep)
    {
      /* This should have a single inference expression child. */
      const struct ASTNode *infer = ARRAY_GET(child->children, struct ASTNode,
        0);
      const struct SolASTNodeData *infer_data =
        get_sol_node_data_c(infer);
      if (infer_data->type != NodeTypeInferenceExpression)
      {
        /* TODO: error. */
        add_error(state->unit, infer_data->location,
          "incorrect node type.");
        return 1;
      }

      /* Locate the symbol. */
      const struct ASTNode *path_node = ARRAY_GET(infer->children,
        struct ASTNode, 0);
      struct ObjectName path = {};
      int err = extract_path(&path, path_node);
      if (err)
      {
        /* TODO: error. */
        add_error(state->unit, infer_data->location,
          "cannot extract path.");
        return 1;
      }
      struct SolObject *thm = lookup_symbol(scope_node, &path);
      free_name(&path);
      if (thm == NULL)
      {
        /* TODO: error. */
        add_error(state->unit, infer_data->location,
          "unknown theorem");
        return 1;
      }

      /* Make a list of arguments. */
      struct ArgumentList args = {};
      const struct ASTNode *args_node = ARRAY_GET(infer->children,
        struct ASTNode, 1);
      const struct SolASTNodeData *args_data =
        get_sol_node_data_c(args_node);

      /* Do we have the same number of arguments as there are parameters? */
      if (ARRAY_LENGTH(args_node->children) != ARRAY_LENGTH(thm->parameters))
      {
        /* TODO: error. */
        add_error(state->unit, args_data->location,
          "incorrect number of arguments supplied.");
        return 1;
      }

      /* Construct the arguments. */
      ARRAY_INIT(args.arguments, struct Argument);
      for (size_t j = 0; j < ARRAY_LENGTH(args_node->children); ++j)
      {
        struct Argument arg = {};
        const struct Parameter *param = ARRAY_GET(thm->parameters,
          struct Parameter, j);
        arg.name = strdup(param->name);

        const struct ASTNode *expr_node = ARRAY_GET(args_node->children,
          struct ASTNode, j);
        const struct SolASTNodeData *expr_data =
          get_sol_node_data_c(expr_node);
        err = validate_expression(state, &arg.value, expr_node, theorem, 0);
        PROPAGATE_ERROR(err);
        ARRAY_APPEND(args.arguments, struct Argument, arg);
      }

      /* Try to add it to the proof environment (check that the assumptions
         are met and then add its inferences). */
      err = instantiate_object(state, thm, &args, &env);
      if (err)
      {
        add_note(state->unit, child_data->location,
          "at this proof step.");
      }
      PROPAGATE_ERROR(err);

      /* Tear down the arguments. */
      for (size_t j = 0; j < ARRAY_LENGTH(args.arguments); ++j)
      {
        struct Argument *arg = ARRAY_GET(args.arguments, struct Argument, j);
        free(arg->name);
        free_expression(&arg->value);
      }
      ARRAY_FREE(args.arguments);
    }
  }

  /* Make sure that each inference has been deduced in the process
     of the proof. */
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->inferences); ++i)
  {
    const struct JudgementInstance *infer = ARRAY_GET(theorem->inferences,
      struct JudgementInstance, i);
    if (!judgement_proved(state, &env, infer))
    {
      /* TODO: error. */
      add_error(state->unit, infer->location,
        "inference not proven");
      return 1;
    }
  }

  /* Tear down the proof environment. */
  for (size_t i = 0; i < ARRAY_LENGTH(env.proven); ++i)
  {
    struct JudgementInstance *proven = ARRAY_GET(env.proven,
      struct JudgementInstance, i);
    for (size_t j = 0; j < ARRAY_LENGTH(proven->expression_args); ++j)
    {
      struct Expression *expr = ARRAY_GET(proven->expression_args,
        struct Expression, j);
      free_expression(expr);
    }
    ARRAY_FREE(proven->expression_args);
  }
  ARRAY_FREE(env.proven);

  /* TODO: verify that adding this will not introduce any collisions. */
  struct Symbol symbol = {
    .name = strdup(get_sol_node_data_c(ast_theorem)->name),
    .object = theorem
  };
  ARRAY_APPEND(scope_data->symbol_table, struct Symbol, symbol);
  return 0;
}

int
validate_namespace(struct ValidationState *state,
  const struct ASTNode *ast_namespace)
{
  int err = 0;

  struct ASTNode *scope_node = state->scope_current;
  struct SolScopeNodeData *scope_data = get_scope_node_data(scope_node);

  const struct SolASTNodeData *ast_data = get_sol_node_data_c(ast_namespace);

  /* Make sure this scope has a unique name. */
  if (scope_node->parent != NULL)
  {
    struct ASTNode *parent = scope_node->parent;
    for (size_t i = 0; i < ARRAY_LENGTH(parent->children); ++i)
    {
      const struct ASTNode *sibling = ARRAY_GET(parent->children,
        struct ASTNode, i);
      const struct SolScopeNodeData *sibling_data =
        get_scope_node_data_c(sibling);
      if (sibling_data == scope_data)
        continue;
      if (strcmp(ast_data->name, sibling_data->name) == 0)
      {
        /* TODO: Error, names must be unique. */
        add_error(state->unit, ast_data->location,
          "namespace names must be unique.");
        return 1;
      }
    }
    scope_data->name = strdup(ast_data->name);
  }

  if (scope_data->name != NULL)
    LOG_NORMAL(state->out, "Validating namespace '%s'.\n", scope_data->name);

  /* Next, initialize the symbol table and search path list. */
  ARRAY_INIT(scope_data->symbol_table, struct Symbol);
  ARRAY_INIT(scope_data->symbol_search_locations, struct ASTNode *);

  /* Finally, loop through the children in the syntax tree and validate them. */
  for (size_t i = 0; i < ARRAY_LENGTH(ast_namespace->children); ++i)
  {
    const struct ASTNode *ast_child =
      ARRAY_GET(ast_namespace->children, struct ASTNode, i);
    const struct SolASTNodeData *ast_child_data =
      get_sol_node_data_c(ast_child);
    switch (ast_child_data->type)
    {
      case NodeTypeNamespace:
        state->scope_current = new_child(scope_node);
        init_scope_node(state->scope_current);
        err = validate_namespace(state, ast_child);
        state->scope_current = scope_node;
        PROPAGATE_ERROR(err);
        break;
      case NodeTypeImport:
        err = validate_import(state, ast_child);
        PROPAGATE_ERROR(err);
        break;
      case NodeTypeJudgement:
        err = validate_judgement(state, ast_child);
        PROPAGATE_ERROR(err);
        break;
      case NodeTypeAxiom:
        err = validate_axiom(state, ast_child);
        PROPAGATE_ERROR(err);
        break;
      case NodeTypeTheorem:
        err = validate_theorem(state, ast_child);
        PROPAGATE_ERROR(err);
        break;
      default:
        add_error(state->unit, ast_child_data->location,
          "incorrect node type.");
        return 1;
        break;
    }
  }

  return 0;
}

int
validate_program(struct ValidationState *state)
{
  init_tree(&state->scope_tree_root);
  state->scope_current = &state->scope_tree_root;
  init_scope_node(state->scope_current);

  int err = validate_namespace(state, &state->input->ast_root);

  /* Free everything. */
  free_tree(&state->scope_tree_root);

  return err;
}

int
sol_verify(const char *input_path, FILE *out)
{
  /* Open the file. */
  LOG_NORMAL(out, "Validating file '%s'.\n", input_path);
  struct CompilationUnit unit = {};
  open_compilation_unit(&unit, input_path);

  /* Lex the file */
  LOG_VERBOSE(out, "Tokenizing.\n");
  struct LexState lex_out = {};

  init_lex_state(&lex_out);
  file_to_lines(&lex_out, &unit);
  remove_whitespace(&lex_out);
  separate_symbols(&lex_out);
  identify_symbols(&lex_out, sol_symbols);
  remove_block_comments(&lex_out, "/*", "*/");
  remove_line_comments(&lex_out, "//");
  separate_identifiers(&lex_out);
  identify_keywords(&lex_out, sol_keywords);
  remove_line_ends(&lex_out);

  /* Parse the file */
  LOG_VERBOSE(out, "Parsing.\n");
  struct ParserState parse_out = {};
  parse_out.unit = &unit;
  parse_out.input = &lex_out;
  parse_out.ast_current = &parse_out.ast_root;

  int err = parse_program(&parse_out);
  if (err)
  {
    print_errors(&unit);
    return 1;
  }
  PROPAGATE_ERROR(err);

  /* Validate the file. */
  LOG_VERBOSE(out, "Validating.\n");
  struct ValidationState validation_out = {};
  validation_out.out = out;
  validation_out.unit = &unit;
  validation_out.input = &parse_out;

  err = validate_program(&validation_out);
  if (err)
    print_errors(&unit);

  /* Free the AST. */
  LOG_VERBOSE(out, "Done.\n");
  free_tree(&parse_out.ast_root);
  free_lex_state(&lex_out);
  PROPAGATE_ERROR(err);

  close_compilation_unit(&unit);

  return 0;
}
