#include "logic.h"
#include "parse.h"
#include <string.h>

const char *sl_keywords[] = {
  "namespace",

  "atomic",

  "use",
  "type",
  "const",
  "expr",
  "axiom",
  "theorem",

  "latex",
  "bind",
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
  "+",
  ".", ",", ";",
  "%", "$", "=",
  "/*", "*/",
  "//",
  NULL
};

struct ValidationState
{
  bool valid;
  FILE *out;

  struct CompilationUnit *unit;
  const struct ParserState *input;

  sl_LogicState *logic;
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
extract_latex_format(struct ValidationState *state,
  const struct ASTNode *latex, struct TheoremEnvironment *env,
  struct PrototypeLatexFormat *dst)
{
  const struct ASTNodeData *data = AST_NODE_DATA(latex);
  if (data->type != ASTNodeTypeLatex)
  {
    add_error(state->unit, data->location,
      "expected a latex format but found the wrong type of node.");
    state->valid = FALSE;
  }

  dst->segments = malloc(sizeof(struct PrototypeLatexFormatSegment *)
    * (ARRAY_LENGTH(latex->children) + 1));
  for (size_t i = 0; i < ARRAY_LENGTH(latex->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(latex->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeLatexString)
    {
      struct PrototypeLatexFormatSegment *seg =
        malloc(sizeof(struct PrototypeLatexFormatSegment));
      seg->is_variable = FALSE;
      seg->string = strdup(child_data->name);
      dst->segments[i] = seg;
    }
    else if (child_data->type == ASTNodeTypeLatexVariable)
    {
      /* Attempt to extract a value from this. */
      struct PrototypeLatexFormatSegment *seg =
        malloc(sizeof(struct PrototypeLatexFormatSegment));
      seg->is_variable = TRUE;
      seg->string = strdup(child_data->name);
      dst->segments[i] = seg;
    }
  }
  dst->segments[ARRAY_LENGTH(latex->children)] = NULL;

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

  if (ARRAY_LENGTH(constant->children) < 1)
  {
    add_error(state->unit, data->location,
      "a constant node must have at least a single child, containing the path to the constant's type");
    state->valid = FALSE;
  }
  const struct ASTNode *type = ARRAY_GET(constant->children, struct ASTNode, 0);

  SymbolPath *local_path = extract_path(state, type);

  proto.type_path = lookup_symbol(state, local_path);
  free_symbol_path(local_path);
  proto.latex.segments = NULL;

  /* Look for latex. */
  struct TheoremEnvironment env;
  init_theorem_environment(&env);
  for (size_t i = 0; i < ARRAY_LENGTH(constant->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(constant->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeLatex)
    {
      int err = extract_latex_format(state, child, &env, &proto.latex);
      PROPAGATE_ERROR(err);
    }
  }
  free_theorem_environment(&env);

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
  struct TheoremEnvironment env;
  init_theorem_environment(&env);

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
    ARRAY_APPEND(env.parameters, struct PrototypeParameter,
      *proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  /* If there are bindings, extract them. */
  size_t binds_n = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(expression->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(expression->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeBind)
      ++binds_n;
  }
  if (binds_n == 0)
  {
    proto.bindings = NULL;
  }
  else
  {
    proto.bindings = malloc(sizeof(Value *) * (binds_n + 1));
    size_t binding_index = 0;
    for (size_t i = 0; i < ARRAY_LENGTH(expression->children); ++i)
    {
      const struct ASTNode *child =
        ARRAY_GET(expression->children, struct ASTNode, i);
      const struct ASTNodeData *child_data = AST_NODE_DATA(child);
      if (child_data->type == ASTNodeTypeBind)
      {
        const struct ASTNode *binding =
          ARRAY_GET(child->children, struct ASTNode, 0);
        proto.bindings[binding_index] = extract_value(state, binding, &env);
        ++binding_index;
      }
    }
    proto.bindings[binds_n] = NULL;
  }

  /* Look for latex. */
  proto.latex.segments = NULL;
  for (size_t i = 0; i < ARRAY_LENGTH(expression->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(expression->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeLatex)
    {
      int err = extract_latex_format(state, child, &env, &proto.latex);
      PROPAGATE_ERROR(err);
    }
  }

  LogicError err = add_expression(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, data->location,
      "cannot add expression to logic state.");
    state->valid = FALSE;
  }

  free_theorem_environment(&env);
  free_symbol_path(proto.expression_path);
  free_symbol_path(proto.expression_type);
  for (size_t i = 0; i < args_n; ++i)
  {
    free(proto.parameters[i]->name);
    free_symbol_path(proto.parameters[i]->type);
    free(proto.parameters[i]);
  }
  free(proto.parameters);
  if (proto.bindings != NULL)
  {
    for (Value **binding = proto.bindings; *binding != NULL; ++binding)
      free_value(*binding);
    free(proto.bindings);
  }

  return 0;
}

static struct PrototypeRequirement *
extract_require(struct ValidationState *state,
  const struct ASTNode *require, struct TheoremEnvironment *env)
{
  struct PrototypeRequirement *dst =
    malloc(sizeof(struct PrototypeRequirement));

  const struct ASTNodeData *data = AST_NODE_DATA(require);
  if (data->type != ASTNodeTypeRequire)
  {
    add_error(state->unit, data->location,
      "expected a requirement but found the wrong type of node.");
    state->valid = FALSE;
  }

  dst->require = strdup(data->name);
  dst->arguments =
    malloc(sizeof(Value *) * (ARRAY_LENGTH(require->children) + 1));

  for (size_t i = 0; i < ARRAY_LENGTH(require->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(require->children, struct ASTNode, i);
    dst->arguments[i] = extract_value(state, child, env);
  }

  dst->arguments[ARRAY_LENGTH(require->children)] = NULL;

  return dst;
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

  size_t requirements_n = 0;
  size_t assumptions_n = 0;
  size_t inferences_n = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(axiom->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(axiom->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeRequire)
      ++requirements_n;
    else if (child_data->type == ASTNodeTypeAssume)
      ++assumptions_n;
    else if (child_data->type == ASTNodeTypeInfer)
      ++inferences_n;
  }
  proto.requirements =
    malloc(sizeof(struct PrototypeRequirement *) * (requirements_n + 1));
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

  size_t require_index = 0;
  size_t assume_index = 0;
  size_t infer_index = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(axiom->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(axiom->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeRequire)
    {
      proto.requirements[require_index] = extract_require(state, child, &env);
      ++require_index;
    }
    else if (child_data->type == ASTNodeTypeDef)
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
  proto.requirements[requirements_n] = NULL;
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
  for (size_t i = 0; i < requirements_n; ++i)
  {
    free(proto.requirements[i]->require);
    for (Value **arg = proto.requirements[i]->arguments; *arg != NULL; ++arg)
    {
      free_value(*arg);
    }
    free(proto.requirements[i]->arguments);
    free(proto.requirements[i]);
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
  free(proto.requirements);
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

  size_t requirements_n = 0;
  size_t assumptions_n = 0;
  size_t inferences_n = 0;
  size_t steps_n = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(theorem->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeRequire)
      ++requirements_n;
    if (child_data->type == ASTNodeTypeAssume)
      ++assumptions_n;
    else if (child_data->type == ASTNodeTypeInfer)
      ++inferences_n;
    else if (child_data->type == ASTNodeTypeStep)
      ++steps_n;
  }
  proto.requirements =
    malloc(sizeof(struct PrototypeRequirement *) * (requirements_n + 1));
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

  size_t require_index = 0;
  size_t assume_index = 0;
  size_t infer_index = 0;
  size_t step_index = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->children); ++i)
  {
    const struct ASTNode *child =
      ARRAY_GET(theorem->children, struct ASTNode, i);
    const struct ASTNodeData *child_data = AST_NODE_DATA(child);
    if (child_data->type == ASTNodeTypeRequire)
    {
      proto.requirements[require_index] = extract_require(state, child, &env);
      ++require_index;
    }
    else if (child_data->type == ASTNodeTypeDef)
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
  proto.requirements[requirements_n] = NULL;
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
  for (size_t i = 0; i < requirements_n; ++i)
  {
    free(proto.requirements[i]->require);
    for (Value **arg = proto.requirements[i]->arguments; *arg != NULL; ++arg)
    {
      free_value(*arg);
    }
    free(proto.requirements[i]->arguments);
    free(proto.requirements[i]);
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
        {
          SymbolPath *use_path = extract_use(state, child);
          ARRAY_APPEND(using_paths, SymbolPath *, use_path);
          ARRAY_APPEND(state->search_paths, SymbolPath *, use_path);
        }
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
  //state->logic = new_logic_state(state->out);
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

  //free_logic_state(state->logic);
  free_symbol_path(state->prefix_path);
  ARRAY_FREE(state->search_paths);
  return 0;
}

int
sl_verify(sl_LogicState *logic_state, const char *input_path, FILE *out)
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
  tokenize_strings(&lex_out, '"');
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
  validation_out.logic = logic_state;

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
