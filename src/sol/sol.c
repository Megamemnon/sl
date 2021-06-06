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
  ".", ",", ";", ":",
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
  int err = parse_expression(state);
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
  int err = parse_expression(state);
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
  const char *step_name;
  if (!consume_identifier(state, &step_name))
  {
    add_error(state, "No step name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeStep;
  get_sol_node_data(state->ast_current)->name = strdup(step_name);

  /* After the name, there should be an expression giving the inferrence. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_expression(state);
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

  /* Next, loop through arguments. */
  int first_arg = 1;
  while (!consume_symbol(state, ")"))
  {
    /* Subsequent arguments have commas. */
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

  return 0;
}

int
parse_expression(struct ParserState *state)
{
  /* First, consume the name of the root-level term. */
  const char *identifier_name;
  if (!consume_identifier(state, &identifier_name))
  {
    add_error(state, "No identifier provided in expression.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeExpression;
  get_sol_node_data(state->ast_current)->name = strdup(identifier_name);

  /* Expect an opening '(' for the argument list, otherwise we have
     a variable. */
  if (!consume_symbol(state, "("))
  {
    return 0;
  }

  /* Next, loop through arguments. */
  int first_arg = 1;
  while (!consume_symbol(state, ")"))
  {
    /* Subsequent arguments have commas. */
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
    int err = parse_parameter(state);
    ascend(state);
    PROPAGATE_ERROR(err);

    if (first_param)
      first_param = 0;
  }

  /* Next, check for a definition. */
  return 0;
}

int
parse_parameter(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeParameter;

  /* Parameters always have the form `[PARAM_NAME]`. */
  const char *parameter_name;
  if (!consume_identifier(state, &parameter_name))
  {
    add_error(state, "No parameter name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->name = strdup(parameter_name);

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
    case NodeTypeIdentifierPath:
      snprintf(buf, len, "Path");
      break;
    case NodeTypeIdentifierPathSegment:
      snprintf(buf, len, "Path Segment<Identifier: \"%s\">", name);
      break;
    case NodeTypeExpression:
      snprintf(buf, len, "Expression<Name: \"%s\">", name);
      break;
    case NodeTypeSubstitutionMap:
      snprintf(buf, len, "Substitution Map");
      break;
    case NodeTypeSubstitution:
      snprintf(buf, len, "Substitution<Destination=\"%s\">", name);
      break;
    case NodeTypeParameterList:
      snprintf(buf, len, "Parameter List");
      break;
    case NodeTypeParameter:
      snprintf(buf, len, "Parameter<Name: \"%s\">", name);
      break;
    default:
      snprintf(buf, len, "Unknown");
      break;
  }
}

#if 0
void
traverse_tree_for_formulas(const struct ASTNode *node, void *userdata)
{
  struct ValidationState *state = (struct ValidationState *)userdata;
  const struct SolASTNodeData *data = get_sol_node_data_c(node);
  if (data->type == NodeTypeFormula)
  {
    struct Formula formula = {};

    formula.global_name = strdup(data->name);

    /* First, find the relevant children. */
    const struct ASTNode *params = NULL;
    const struct ASTNode *expression = NULL;

    for (size_t i = 0; i < ARRAY_LENGTH(node->children); ++i)
    {
      const struct ASTNode *child =
        ARRAY_GET(node->children, struct ASTNode, i);
      const struct SolASTNodeData *child_data =
        get_sol_node_data_c(child);

      if (child_data->type == NodeTypeParameterList)
        params = child;
      if (child_data->type == NodeTypeFormulaExpression)
        expression = child;
    }

    /* TODO: check to make sure these nodes exist! (These checks should have
       been made during parsing, but should still be made in the case that
       we are provided with an AST constructed differently). */
    /* Enumerate all the parameters. */
    for (size_t i = 0; i < ARRAY_LENGTH(params->children); ++i)
    {
      const struct ASTNode *child =
        ARRAY_GET(params->children, struct ASTNode, i);
      struct Parameter param = {};
      param.name = strdup(get_sol_node_data_c(child)->name);
      const char *type = get_sol_node_data_c(child)->data_type;
      if (strcmp(type, "Formula") == 0)
      {
        param.type = ParameterTypeFormula;
      }
      else if (strcmp(type, "Var") == 0)
      {
        param.type = ParameterTypeVar;
      }
      else
      {
        /* TODO: error, unknown type. */
      }
      ARRAY_APPEND(formula.parameters, struct Parameter, param);
    }

    /* Copy over the expression, if the formula is not atomic. */
    if (expression != NULL)
    {
      struct ASTNode *expression_copy = malloc(sizeof(struct ASTNode));
      memset(expression_copy, 0, sizeof(struct ASTNode));
      copy_tree(expression_copy, expression);
      formula.expression = expression_copy;

      /* Finally, validate the formula before adding it. */
      if (validate_expression(state, formula.expression,
          formula.parameters.data, ARRAY_LENGTH(formula.parameters)))
      {
        /* TODO: Error, invalid formula. */
        printf("stummy hurt\n");
      }
    }

    ARRAY_APPEND(state->formulas, struct Formula, formula);
  }
}

int
validate_expression(const struct ValidationState *state,
  const struct ASTNode *expression,
  const struct Parameter *parameters, size_t parameters_n)
{
  const char *formula_name = get_sol_node_data_c(expression)->name;
  /* The argument may be referencing a parameter, so in this case, defer
     validation of this part until substitution. */
  for (size_t i = 0; i < parameters_n; ++i)
  {
    if (strcmp(parameters[i].name, formula_name) == 0)
      return 0;
  }

  const struct Formula *formula = NULL;
  /* Locate the formula being referenced. */
  for (size_t i = 0; i < ARRAY_LENGTH(state->formulas); ++i)
  {
    const struct Formula *f =
      ARRAY_GET(state->formulas, struct Formula, i);
    if (strcmp(f->global_name, formula_name) == 0)
      formula = f;
  }

  if (formula == NULL)
  {
    /* TODO: Error, formula referenced does not exist. */
    return 1;
  }

  /* Now that we have located the formula, loop through the arguments provided
     and recursively verify them. */
  Array args_provided;
  ARRAY_INIT(args_provided, struct ASTNode);
  for (size_t i = 0; i < ARRAY_LENGTH(expression->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(expression->children, struct ASTNode, i);
    if (get_sol_node_data_c(child)->type
        == NodeTypeFormulaExpression)
      ARRAY_APPEND(args_provided, struct ASTNode, *child);
  }

  /* Do we have the correct number of arguments? */
  if (ARRAY_LENGTH(args_provided) != ARRAY_LENGTH(formula->parameters))
  {
    /* TODO: Error, incorrect number of arguments. */
    return 1;
  }

  int err;
  for (size_t i = 0; i < ARRAY_LENGTH(args_provided); ++i)
  {
    /* TODO: Do the types agree? */
    struct ASTNode *argument =
      ARRAY_GET(args_provided, struct ASTNode, i);
    err = validate_expression(state, argument, parameters,
      parameters_n);
    PROPAGATE_ERROR(err);
  }

  ARRAY_FREE(args_provided);

  return 0;
}

void
traverse_tree_for_axioms(const struct ASTNode *node, void *userdata)
{
  struct ValidationState *state = (struct ValidationState *)userdata;
  const struct SolASTNodeData *data = get_sol_node_data_c(node);
  if (data->type == NodeTypeAxiom)
  {
#if 0
    struct Axiom axiom = {};
    ARRAY_INIT(axiom.parameters, axiom.parameters_n);
    ARRAY_INIT(axiom.hypotheses, axiom.hypotheses_n);

    /* First, find the relevant children. */
    const struct ASTNode *params = NULL;
    const struct ASTNode *expression = NULL;

    for (size_t i = 0; i < node->children_n; ++i)
    {
      const struct SolASTNodeData *child_data =
        get_sol_node_data_c(&node->children[i]);

      if (child_data->type == NodeTypeParameterList)
        params = &node->children[i];
      if (child_data->type == NodeTypeFormulaExpression)
        expression = &node->children[i];
    }

    /* TODO: check to make sure these exist! (These checks should have
       been made during parsing, but should still be made in the case that
       we are provided with an AST constructed differently). */
    /* Enumerate all the parameters. */
    for (size_t i = 0; i < params->children_n; ++i)
    {
      struct Parameter param = {};
      param.name = strdup(get_sol_node_data_c(&params->children[i])->name);
      const char *type = get_sol_node_data_c(&params->children[i])->data_type;
      if (strcmp(type, "Formula") == 0)
      {
        param.type = ParameterTypeFormula;
      }
      else if (strcmp(type, "Var") == 0)
      {
        param.type = ParameterTypeVar;
      }
      else
      {
        /* TODO: error, unknown type. */
      }
      ARRAY_APPEND(param, formula.parameters, formula.parameters_n);
    }

    /* Copy over the expression, if the formula is not atomic. */
    if (expression != NULL)
    {
      struct ASTNode *expression_copy = malloc(sizeof(struct ASTNode));
      memset(expression_copy, 0, sizeof(struct ASTNode));
      copy_tree(expression_copy, expression);
      formula.expression = expression_copy;
    }

    ARRAY_APPEND(axiom, state->axioms, state->axioms_n);
#endif
  }
}

void
traverse_tree_for_theorems(const struct ASTNode *node, void *userdata)
{
  struct ValidationState *state = (struct ValidationState *)userdata;
  const struct SolASTNodeData *data = get_sol_node_data_c(node);
  if (data->type == NodeTypeTheorem)
  {
    struct Theorem theorem = {};

    ARRAY_APPEND(state->theorems, struct Theorem, theorem);
  }
}

int
validate_program(struct ValidationState *state)
{
  /* Traverse the tree in three steps: formulas, axioms, and theorems. Each step
     is validated based on the previous steps (atomic formulas are always
     valid, compound formulas are valid if they are syntactically valid,
     then axioms are valid if they consist of well-formed formulas,
     and theorems are valid if they have a valid proof from the axioms). */
  ARRAY_INIT(state->formulas, struct Formula);
  ARRAY_INIT(state->axioms, struct Axiom);
  ARRAY_INIT(state->theorems, struct Theorem);

  traverse_tree(&state->input->ast_root, &traverse_tree_for_formulas, state);
  traverse_tree(&state->input->ast_root, &traverse_tree_for_axioms, state);
  traverse_tree(&state->input->ast_root, &traverse_tree_for_theorems, state);

  return 0;
}
#endif

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

  print_tree(&parse_out.ast_root, &print_sol_node);

  /* Free the token list. */
  free_lex_result(&lex_out);
  PROPAGATE_ERROR(err);

  /* Validate the file. */
  //struct ValidationState validation_out = {};
  //validation_out.input = &parse_out;

  //validate_program(&validation_out);

  /* Free the AST. */
  free_tree(&parse_out.ast_root);
  PROPAGATE_ERROR(err);

  return 0;
}
