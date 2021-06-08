#include "sol.h"
#include <parse.h>
#include <common.h>

#include <string.h>

// TODO: remove debug stuff
#include <stdio.h>

const char *sol_keywords[] = {
  "namespace",
  "import",

  "judgement",
  "axiom",
  "theorem",

  "assume",
  "infer",
  "step",
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
  while (state->token_index < ARRAY_LENGTH(state->input->tokens)
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
      add_error(state, "Unrecognized token.");
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
    add_error(state, "No name provided for namespace.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeNamespace;
  get_sol_node_data(state->ast_current)->name = strdup(namespace_name);

  /* Then there should be an opening bracket. */
  if (!consume_symbol(state, "{"))
  {
    add_error(state, "Expected '{' following namespace name.");
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

  /* Iterate through the list of paths until we find a ';' */
  int first_path = 1;
  while (!consume_symbol(state, ";"))
  {
    /* Subsequent paths have commas. */
    if (!first_path && !consume_symbol(state, ","))
    {
      /* TODO: error: no separator. */
      add_error(state, "No separator in path list.");
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
    add_error(state, "No judgement name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeJudgement;
  get_sol_node_data(state->ast_current)->name = strdup(judgement_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state, "No parameter list provided.");
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
    add_error(state, "Expected ';' after expression.");
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
    add_error(state, "Axioms must have a name.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeAxiom;
  get_sol_node_data(state->ast_current)->name = strdup(axiom_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state, "Axioms must have a list of parameters.");
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
    add_error(state, "Axioms must have a definition");
    return 1;
  }

  while (state->token_index < ARRAY_LENGTH(state->input->tokens)
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
    else
    {
      add_error(state, "Unrecognized token.");
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
    add_error(state, "No theorem name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeTheorem;
  get_sol_node_data(state->ast_current)->name = strdup(theorem_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state, "No parameter list provided.");
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
    add_error(state, "Theorems must have a statement and proof.");
    return 1;
  }

  while (state->token_index < ARRAY_LENGTH(state->input->tokens)
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
    else
    {
      add_error(state, "Unrecognized token.");
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

  /* There should be an expression for a judgement. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_judgement_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state, "Expected ';' after assumption.");
    return 1;
  }
  return 0;
}

int
parse_infer(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeInfer;

  /* After the keyword, there should be a judgement expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_judgement_expression(state);
  PROPAGATE_ERROR(err);
  ascend(state);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state, "Expected ';' after inferrence.");
    return 1;
  }
  return 0;
}

int
parse_step(struct ParserState *state)
{
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
    add_error(state, "Expected ';' after proof step.");
    return 1;
  }

  return 0;
}

int
parse_judgement_expression(struct ParserState *state)
{
  /* First, consume the name of the root-level term. */
  const char *judgement_name;
  if (!consume_identifier(state, &judgement_name))
  {
    add_error(state, "No judgement provided in expression.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeJudgementExpression;
  get_sol_node_data(state->ast_current)->name = strdup(judgement_name);

  /* Expect an opening '(' for the argument list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state, "No argument list provided in expression.");
    return 1;
  }

  /* Next, parse arguments. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_argument_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  return 0;
}

int
parse_inference_expression(struct ParserState *state)
{
  /* First, consume the name of the root-level term. */
  const char *inference_name;
  if (!consume_identifier(state, &inference_name))
  {
    add_error(state, "No inference provided in expression.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeInferenceExpression;
  get_sol_node_data(state->ast_current)->name = strdup(inference_name);

  /* Expect an opening '(' for the argument list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state, "No argument list provided in expression.");
    return 1;
  }

  /* Next, parse arguments. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_argument_list(state);
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
    add_error(state, "Expressions must start with '\\'.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeExpression;

  /* Loop through the expression until we find a terminating backslash. */
  while (!consume_symbol(state, "\\"))
  {
    /* If there is a '$' symbol, parse the variable expression. */
    if (consume_symbol(state, "$"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      int err = parse_expression_variable(state);
      ascend(state);
      PROPAGATE_ERROR(err);
    }
    else
    {
      /* Otherwise, just add the symbol as a "constant". */
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      get_sol_node_data(state->ast_current)->type = NodeTypeExpressionConstant;
      get_sol_node_data(state->ast_current)->name =
        strdup(get_current_token(state)->value);
      ascend(state);
      advance(state);
    }
  }

  return 0;
}

int
parse_expression_variable(struct ParserState *state)
{
  /* First, expect an identifier for the name of the variable. */
  const char *variable_name;
  if (!consume_identifier(state, &variable_name))
  {
    add_error(state, "Variable name expected.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeExpressionVariable;
  get_sol_node_data(state->ast_current)->name = strdup(variable_name);

  /* There might be a substitution map. */
  if (consume_symbol(state, "["))
  {
    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    int err = parse_substitution_map(state);
    ascend(state);
    PROPAGATE_ERROR(err);
  }

  return 0;
}

int
parse_substitution_map(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeSubstitutionMap;

  /* Iterate through the list until we get a closing ']' */
  int first_param = 1;
  while (!consume_symbol(state, "]"))
  {
    /* Subsequent substitutions have commas. */
    if (!first_param && !consume_symbol(state, ","))
    {
      add_error(state, "Substitutions must be comma-separated.");
      return 1;
    }

    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    int err = parse_substitution(state);
    ascend(state);
    PROPAGATE_ERROR(err);

    if (first_param)
      first_param = 0;
  }

  return 0;
}

int
parse_substitution(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeSubstitution;

  /* Parameters always have the form `[SUBSTITUTION_DEST] = [SUBSTITUTION_SRC]`. */
  const char *dst_name;
  if (!consume_identifier(state, &dst_name))
  {
    add_error(state, "No destination provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->name = strdup(dst_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "="))
  {
    add_error(state, "After the substitution destination, the substitution source follows a '='.");
    return 1;
  }

  /* Then the source is an expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  return 0;
}

int
parse_identifier_path(struct ParserState *state)
{
  /* We should always start with an identifier, and then alternate between dots
     and identifiers. */
  get_sol_node_data(state->ast_current)->type = NodeTypeIdentifierPath;
  const char *seg;
  if (!consume_identifier(state, &seg))
  {
    add_error(state, "An identifier path needs at least one segment.");
    return 1;
  }

  /* TODO: should this be its own function? */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  get_sol_node_data(state->ast_current)->type = NodeTypeIdentifierPathSegment;
  get_sol_node_data(state->ast_current)->name = strdup(seg);
  ascend(state);

  while (consume_symbol(state, "."))
  {
    if (!consume_identifier(state, &seg))
    {
      add_error(state,
        "All segments in an identifier path must be identifiers");
      return 1;
    }
    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    get_sol_node_data(state->ast_current)->type = NodeTypeIdentifierPathSegment;
    get_sol_node_data(state->ast_current)->name = strdup(seg);
    ascend(state);
  }

  return 0;
}

int
parse_parameter_list(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeParameterList;

  /* Iterate through the list until we get a closing ')' */
  int first_param = 1;
  while (!consume_symbol(state, ")"))
  {
    /* Subsequent parameters have commas. */
    if (!first_param && !consume_symbol(state, ","))
    {
      add_error(state, "Parameters must be comma-separated.");
      return 1;
    }

    add_child_and_descend(state);
    init_sol_node(state->ast_current);
    get_sol_node_data(state->ast_current)->type = NodeTypeParameter;
    /* Parameters always have the form `[PARAM_NAME]`. */
    const char *parameter_name;
    if (!consume_identifier(state, &parameter_name))
    {
      add_error(state, "No parameter name provided.");
      return 1;
    }
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

  /* Iterate through the list until we get a closing ')' */
  int first_arg = 1;
  while (!consume_symbol(state, ")"))
  {
    /* Subsequent parameters have commas. */
    if (!first_arg && !consume_symbol(state, ","))
    {
      add_error(state, "Arguments must be comma-separated.");
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
    case NodeTypeSubstitutionMap:
      snprintf(buf, len, "Substitution Map");
      break;
    case NodeTypeSubstitution:
      snprintf(buf, len, "Substitution<Destination=\"%s\">", name);
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

void
free_scope_node(struct ASTNode *node)
{

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

int
names_equal(const struct ObjectName *a, const struct ObjectName *b)
{
  if (ARRAY_LENGTH(a->segments) != ARRAY_LENGTH(b->segments))
    return 0;
  for (size_t i = 0; i < ARRAY_LENGTH(a->segments); ++i)
  {
    if (strcmp(ARRAY_GET(a->segments, struct ObjectNameSegment, i)->name,
        ARRAY_GET(b->segments, struct ObjectNameSegment, i)->name) != 0)
      return 0;
  }
  return 1;
}

#if 0
int
name_used(struct ValidationState *state,
  const struct ObjectName *name)
{
  /* Loop through the existing objects and compare names. */
  for (size_t i = 0; i < ARRAY_LENGTH(state->judgements); ++i)
  {
    if (names_equal(name,
        &(ARRAY_GET(state->judgements, struct Judgement, i)->name)))
      return 1;
  }
  for (size_t i = 0; i < ARRAY_LENGTH(state->theorems); ++i)
  {
    if (names_equal(name,
        &(ARRAY_GET(state->theorems, struct Theorem, i)->name)))
      return 1;
  }
  return 0;
}
#endif

char *
name_to_string(const struct ObjectName *name)
{
  size_t total_length = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(name->segments); ++i)
  {
    const struct ObjectNameSegment *segment =
      ARRAY_GET(name->segments, struct ObjectNameSegment, i);
    total_length += strlen(segment->name);
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

    const struct ObjectNameSegment *segment =
      ARRAY_GET(name->segments, struct ObjectNameSegment, i);
    strncpy(current, segment->name, strlen(segment->name));
    current += strlen(segment->name);

    if (first_segment)
      first_segment = 0;
  }

  buf[total_length] = '\0';

  return buf;
}

#if 0
int
validate_judgement(struct ValidationState *state,
  const struct ASTNode *judgement)
{
  const struct SolASTNodeData *data = get_sol_node_data_c(judgement);

  /* Check that the name is okay. */
  struct Judgement judgement_obj = {};
  ARRAY_INIT(judgement_obj.name.segments, struct ObjectNameSegment);

  struct ObjectNameSegment segment;

  for (size_t i = 0; i < ARRAY_LENGTH(state->current_scope.segments); ++i)
  {
    segment.name = strdup(ARRAY_GET(state->current_scope.segments,
      struct ObjectNameSegment, i)->name);
    ARRAY_APPEND(judgement_obj.name.segments,
      struct ObjectNameSegment, segment);
  }

  segment.name = strdup(data->name);
  ARRAY_APPEND(judgement_obj.name.segments, struct ObjectNameSegment, segment);

  if (name_used(state, &judgement_obj.name))
  {
    /* TODO: error. */
    return 1;
  }

  /* Find the list of parameters. */
  const struct ASTNode *parameter_list =
    ARRAY_GET(judgement->children, struct ASTNode, 0);
  const struct SolASTNodeData *parameter_list_data =
    get_sol_node_data_c(parameter_list);
  if (parameter_list_data->type != NodeTypeParameterList)
  {
    /* TODO: error. */
    return 1;
  }

  judgement_obj.parameters_n = ARRAY_LENGTH(parameter_list->children);

  ARRAY_APPEND(state->judgements, struct Judgement, judgement_obj);

  return 0;
}

int
validate_assume(struct ValidationState *state,
  const struct ASTNode *assume,
  const struct Theorem *env)
{
  const struct SolASTNodeData *data = get_sol_node_data_c(assume);

  /* This should have a single child that is a judgement expression. */
  const struct ASTNode *judgement_expression =
    ARRAY_GET(assume->children, struct ASTNode, 0);
  const struct SolASTNodeData *judgement_expression_data =
    get_sol_node_data_c(judgement_expression);
  if (judgement_expression_data->type != NodeTypeJudgementExpression)
  {
    /* TODO: error. */
    return 1;
  }

  /* Lookup the judgement expression. */

  return 0;
}

int
validate_infer(struct ValidationState *state,
  const struct ASTNode *infer,
  const struct Theorem *env)
{
  return 0;
}

int
validate_axiom(struct ValidationState *state,
  const struct ASTNode *axiom)
{
  const struct SolASTNodeData *data = get_sol_node_data_c(axiom);

  /* Check that the name is okay. */
  struct Theorem axiom_obj = {};
  ARRAY_INIT(axiom_obj.name.segments, struct ObjectNameSegment);

  struct ObjectNameSegment segment;

  for (size_t i = 0; i < ARRAY_LENGTH(state->current_scope.segments); ++i)
  {
    segment.name = strdup(ARRAY_GET(state->current_scope.segments,
      struct ObjectNameSegment, i)->name);
    ARRAY_APPEND(axiom_obj.name.segments,
      struct ObjectNameSegment, segment);
  }

  segment.name = strdup(data->name);
  ARRAY_APPEND(axiom_obj.name.segments, struct ObjectNameSegment, segment);

  if (name_used(state, &axiom_obj.name))
  {
    /* TODO: error. */
    return 1;
  }

  /* Next, enumerate the parameters. */
  ARRAY_INIT(axiom_obj.parameters, struct Parameter);
  const struct ASTNode *parameter_list =
    ARRAY_GET(axiom->children, struct ASTNode, 0);
  const struct SolASTNodeData *parameter_list_data =
    get_sol_node_data_c(parameter_list);
  if (parameter_list_data->type != NodeTypeParameterList)
  {
    /* TODO: error. */
    return 1;
  }

  for (size_t i = 0; i < ARRAY_LENGTH(parameter_list->children); ++i)
  {
    const struct ASTNode *parameter =
      ARRAY_GET(parameter_list->children, struct ASTNode, i);
    const struct SolASTNodeData *parameter_data =
      get_sol_node_data_c(parameter);
    if (parameter_data->type != NodeTypeParameter)
    {
      /* TODO: error. */
      return 1;
    }
    struct Parameter parameter_obj;
    parameter_obj.name = strdup(parameter_data->name);
    ARRAY_APPEND(axiom_obj.parameters, struct Parameter,
      parameter_obj);
  }

  /* Next, go through assumptions and inferences. */
  int err = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(axiom->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(axiom->children, struct ASTNode, i);
    const struct SolASTNodeData *child_data = get_sol_node_data_c(child);
    switch (child_data->type)
    {
      case NodeTypeAssume:
        err = validate_assume(state, child, &axiom_obj);
        PROPAGATE_ERROR(err);
        break;
      case NodeTypeInfer:
        err = validate_infer(state, child, &axiom_obj);
        PROPAGATE_ERROR(err);
        break;
      default:
        break;
    }
  }

  ARRAY_APPEND(state->theorems, struct Theorem, axiom_obj);

  return 0;
}
#endif

int
validate_import(struct ValidationState *state,
  const struct ASTNode *import)
{
  /* Add the import path to the list of search paths. */
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
        return 1;
      }
    }
    scope_data->name = strdup(ast_data->name);
  }

  /* Next, initialize the symbol table and search path list. */
  ARRAY_INIT(scope_data->symbol_table, struct Symbol);
  ARRAY_INIT(scope_data->symbol_search_paths, struct ObjectName);

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
        break;
      case NodeTypeJudgement:
        //err = validate_judgement(state, child);
        //PROPAGATE_ERROR(err);
        break;
      case NodeTypeAxiom:
        //err = validate_axiom(state, child);
        //PROPAGATE_ERROR(err);
        break;
      case NodeTypeTheorem:
        break;
      default:
        return 1;
        break;
    }
  }

  return 0;
}

int
validate_program(struct ValidationState *state)
{
  /* Traverse the tree in three steps: formulas, axioms, and theorems. Each step
     is validated based on the previous steps (atomic formulas are always
     valid, compound formulas are valid if they are syntactically valid,
     then axioms are valid if they consist of well-formed formulas,
     and theorems are valid if they have a valid proof from the axioms). */
  init_tree(&state->scope_tree_root);
  state->scope_current = &state->scope_tree_root;
  init_scope_node(state->scope_current);

  int err = validate_namespace(state, &state->input->ast_root);
#if 0
  /* TODO: remove temporary debug prints. */
  printf("Judgements:\n");
  for (size_t i = 0; i < ARRAY_LENGTH(state->judgements); ++i)
  {
    const struct Judgement *judgement =
      ARRAY_GET(state->judgements, struct Judgement, i);
    char *name = name_to_string(&judgement->name);
    printf("Judgement<Name: \"%s\", %zu Parameters>\n", name,
      judgement->parameters_n);
    free(name);
  }

  printf("Theorems:\n");
  for (size_t i = 0; i < ARRAY_LENGTH(state->theorems); ++i)
  {
    const struct Theorem *theorem =
      ARRAY_GET(state->theorems, struct Theorem, i);
    char *name = name_to_string(&theorem->name);
    printf("Theorem<Name: \"%s\">\n", name);
    free(name);
  }
#endif

  //ARRAY_FREE(state->judgements);
  //ARRAY_FREE(state->theorems);
  //ARRAY_FREE(state->current_scope.segments);

  return err;
}

int
sol_verify(const char *file_path)
{
  /* Lex the file */
  struct LexResult lex_out = {};

  file_to_lines(&lex_out, file_path);
  remove_whitespace(&lex_out, &lex_out);
  separate_symbols(&lex_out, &lex_out);
  identify_symbols(&lex_out, &lex_out, sol_symbols);
  remove_line_comments(&lex_out, &lex_out, "//");
  remove_block_comments(&lex_out, &lex_out, "/*", "*/");
  separate_identifiers(&lex_out, &lex_out);
  identify_keywords(&lex_out, &lex_out, sol_keywords);
  remove_line_ends(&lex_out, &lex_out);

  /* Parse the file */
  struct ParserState parse_out = {};
  parse_out.input = &lex_out;
  parse_out.ast_current = &parse_out.ast_root;

  int err = parse_program(&parse_out);
  if (err)
  {
    printf("error\n");
    //printf("Error %s\n", parse_out.errors[0].error_msg);
  }

  //print_tree(&parse_out.ast_root, &print_sol_node);

  /* Free the token list. */
  free_lex_result(&lex_out);
  PROPAGATE_ERROR(err);

  /* Validate the file. */
  struct ValidationState validation_out = {};
  validation_out.input = &parse_out;

  err = validate_program(&validation_out);

  /* Free the AST. */
  free_tree(&parse_out.ast_root);
  PROPAGATE_ERROR(err);

  return 0;
}
