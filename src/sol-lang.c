#include "sol-lang.h"
#include "parse.h"
#include "common.h"

#include <string.h>

// TODO: remove debug stuff
#include <stdio.h>

const char *sol_keywords[] = {
  "namespace",
  "import",
  "formula",
  "hypothesis",
  "infer",
  "axiom",
  "theorem",
  "let",
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
  if (data->data_type != NULL)
    free(data->data_type);

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

  if (src_data->data_type != NULL)
    dst_data->data_type = strdup(src_data->data_type);
  else
    dst_data->data_type = NULL;

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

/* Called at the start of parsing. Almost equivalent to
   `parse_namespace`, except no curly braces. */
int
parse_program(struct ParserState *state)
{
  init_sol_node(state->ast_current);
  get_sol_node_data(state->ast_current)->type = NodeTypeNamespace;
  return parse_namespace_interior(state);
}

/* A namespace, which is just a container for other objects:
     - Namespaces
     - Rules
     - Formulas
     - Theorems
     - Axioms */
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
parse_namespace_interior(struct ParserState *state)
{
  int err = 0;
  while (state->token_index < state->input->tokens_n
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
    else if (consume_keyword(state, "formula"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_formula(state);
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
    else if (consume_keyword(state, "axiom"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_axiom(state);
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
      add_error(state, "All segments in an identifier path must be identifiers");
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
parse_formula(struct ParserState *state)
{
  const char *formula_name;
  if (!consume_identifier(state, &formula_name))
  {
    add_error(state, "No formula name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeFormula;
  get_sol_node_data(state->ast_current)->name = strdup(formula_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, "("))
  {
    add_error(state, "No formula parameter list provided.");
    return 1;
  }
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_parameter_list(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* If we have a semicolon, the formula is atomic (no definition in terms of
     other formulas). */
  if (consume_symbol(state, ";"))
    return 0;

  /* Otherwise, there is a definition inside curly brackets. */
  if (!consume_symbol(state, "{"))
  {
    add_error(state, "No formula definition provided.");
    return 1;
  }

  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  err = parse_formula_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon after the expression. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state, "Expected ';' after expression.");
    return 1;
  }

  if (!consume_symbol(state, "}"))
  {
    add_error(state, "'}' expected after formula definition.");
    return 1;
  }

  return 0;
}

int
parse_formula_expression(struct ParserState *state)
{
  /* First, consume the name of the root-level formula. */
  const char *formula_name;
  if (!consume_identifier(state, &formula_name))
  {
    add_error(state, "No formula name provided in expression.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeFormulaExpression;
  get_sol_node_data(state->ast_current)->name = strdup(formula_name);

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
    int err = parse_formula_expression(state);
    ascend(state);
    PROPAGATE_ERROR(err);

    if (first_arg)
      first_arg = 0;
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

  while (state->token_index < state->input->tokens_n
         && !consume_symbol(state, "}"))
  {
    if (consume_keyword(state, "hypothesis"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_hypothesis(state);
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
parse_hypothesis(struct ParserState *state)
{
  const char *hypothesis_name;
  if (!consume_identifier(state, &hypothesis_name))
  {
    add_error(state, "No hypothesis name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeHypothesis;
  get_sol_node_data(state->ast_current)->name = strdup(hypothesis_name);

  /* After the name, there should be a formula expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_formula_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state, "Expected ';' after hypothesis.");
    return 1;
  }
  return 0;
}

int
parse_infer(struct ParserState *state)
{
  get_sol_node_data(state->ast_current)->type = NodeTypeInfer;

  /* After the keyword, there should be a formula expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_formula_expression(state);
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

  while (state->token_index < state->input->tokens_n
         && !consume_symbol(state, "}"))
  {
    if (consume_keyword(state, "hypothesis"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_hypothesis(state);
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
    else if (consume_keyword(state, "let"))
    {
      add_child_and_descend(state);
      init_sol_node(state->ast_current);
      err = parse_let(state);
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
parse_let(struct ParserState *state)
{
  const char *let_name;
  if (!consume_identifier(state, &let_name))
  {
    add_error(state, "No name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->type = NodeTypeLet;
  get_sol_node_data(state->ast_current)->name = strdup(let_name);

  /* After the name, there should be a formula expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_formula_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state, "Expected ';' after 'let' definition.");
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

  /* After the name, there should be a formula expression. */
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  int err = parse_formula_expression(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* In square brackets, we will then have a substitution map. */
  if (!consume_symbol(state, "["))
  {
    add_error(state, "Proof steps must have a substitution map.");
    return 1;
  }
  add_child_and_descend(state);
  init_sol_node(state->ast_current);
  err = parse_substitution_map(state);
  ascend(state);
  PROPAGATE_ERROR(err);

  /* Expect a semicolon. */
  if (!consume_symbol(state, ";"))
  {
    add_error(state, "Expected ';' after step.");
    return 1;
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
  int err = parse_formula_expression(state);
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

  /* Parameters always have the form `[PARAM_NAME] : [PARAM_TYPE]`. */
  const char *parameter_name;
  if (!consume_identifier(state, &parameter_name))
  {
    add_error(state, "No parameter name provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->name = strdup(parameter_name);

  /* After the name, there should be a parameter list. */
  if (!consume_symbol(state, ":"))
  {
    add_error(state, "After a parameter name, the type must be declared following a ':'.");
    return 1;
  }

  const char *parameter_type;
  if (!consume_identifier(state, &parameter_type))
  {
    add_error(state, "No parameter type provided.");
    return 1;
  }
  get_sol_node_data(state->ast_current)->data_type = strdup(parameter_type);

  return 0;
}

void
print_sol_node(char *buf, size_t len, const struct ASTNode *node)
{
  const struct SolASTNodeData *data = get_sol_node_data_c(node);
  const char *name = data->name;
  const char *data_type = data->data_type;
  switch (get_sol_node_data_c(node)->type)
  {
    case NodeTypeNamespace:
      if (name == NULL)
        snprintf(buf, len, "Namespace<Unnamed>");
      else
        snprintf(buf, len, "Namespace<Name: \"%s\">", name);
      break;
    case NodeTypeFormula:
      snprintf(buf, len, "Formula<Name: \"%s\">", name);
      break;
    case NodeTypeFormulaExpression:
      snprintf(buf, len, "Formula Expression<Name: \"%s\">", name);
      break;
    case NodeTypeImport:
      snprintf(buf, len, "Import");
      break;
    case NodeTypeIdentifierPath:
      snprintf(buf, len, "Path");
      break;
    case NodeTypeIdentifierPathSegment:
      snprintf(buf, len, "Path Segment<Identifier: \"%s\">", name);
      break;
    case NodeTypeAxiom:
      snprintf(buf, len, "Axiom<Name: \"%s\">", name);
      break;
    case NodeTypeHypothesis:
      snprintf(buf, len, "Hypothesis<Name: \"%s\">", name);
      break;
    case NodeTypeInfer:
      snprintf(buf, len, "Infer");
      break;
    case NodeTypeTheorem:
      snprintf(buf, len, "Theorem<Name: \"%s\">", name);
      break;
    case NodeTypeLet:
      snprintf(buf, len, "Let<Name: \"%s\">", name);
      break;
    case NodeTypeStep:
      snprintf(buf, len, "Step<Name: \"%s\">", name);
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
      snprintf(buf, len, "Parameter<Name: \"%s\", Type: \"%s\">", name,
        data_type);
      break;
    default:
      snprintf(buf, len, "Unknown");
      break;
  }
}

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

    for (size_t i = 0; i < node->children_n; ++i)
    {
      const struct SolASTNodeData *child_data =
        get_sol_node_data_c(&node->children[i]);

      if (child_data->type == NodeTypeParameterList)
        params = &node->children[i];
      if (child_data->type == NodeTypeFormulaExpression)
        expression = &node->children[i];
    }

    /* TODO: check to make sure these nodes exist! (These checks should have
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

    /* Finally, validate the formula before adding it. */
    if (!validate_new_formula(state, &formula))
    {
      /* TODO: Error, invalid formula. */
    }

    ARRAY_APPEND(formula, state->formulas, state->formulas_n);
  }
}

int
validate_new_formula(const struct ValidationState *state,
  const struct Formula *formula)
{
  /* First, check for uniqueness issues (this is the only formula of this
     exact name in the namespace), then in the case that the formula is not
     atomic, check that its definition is well-formed, by verifying that the
     formulas referenced exist and agree in type signature. */
  /* TODO: Allow formulas to be overloaded. */

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

    ARRAY_APPEND(theorem, state->theorems, state->theorems_n);
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
  traverse_tree(&state->input->ast_root, &traverse_tree_for_formulas, state);
  traverse_tree(&state->input->ast_root, &traverse_tree_for_axioms, state);
  traverse_tree(&state->input->ast_root, &traverse_tree_for_theorems, state);

  return 0;
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
  ARRAY_INIT(parse_out.ast_root.children, parse_out.ast_root.children_n);
  ARRAY_INIT(parse_out.errors, parse_out.errors_n);

  int err = parse_program(&parse_out);
  if (err)
  {
    printf("Error %s\n", parse_out.errors[0].error_msg);
  }

  /* Free the token list. */
  free_lex_result(&lex_out);
  PROPAGATE_ERROR(err);

  /* Validate the file. */
  struct ValidationState validation_out = {};
  validation_out.input = &parse_out;
  ARRAY_INIT(validation_out.formulas, validation_out.formulas_n);
  ARRAY_INIT(validation_out.axioms, validation_out.axioms_n);
  ARRAY_INIT(validation_out.theorems, validation_out.theorems_n);

  validate_program(&validation_out);

  /* Free the AST. */
  free_tree(&parse_out.ast_root);
  PROPAGATE_ERROR(err);

  return 0;
}
