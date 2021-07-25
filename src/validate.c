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
extract_path(struct ValidationState *state, const sl_ASTNode *path)
{
  if (sl_node_get_type(path) != sl_ASTNodeType_Path)
  {
    add_error(state->unit, sl_node_get_location(path),
      "expected a path but found the wrong type of node.");
    state->valid = FALSE;
    return NULL;
  }

  SymbolPath *dst = init_symbol_path();
  for (size_t i = 0; i < sl_node_get_child_count(path); ++i)
  {
    const sl_ASTNode *seg = sl_node_get_child(path, i);
    if (sl_node_get_type(seg) != sl_ASTNodeType_PathSegment)
    {
      add_error(state->unit, sl_node_get_location(seg),
        "expected a path segment but found the wrong type of node.");
      state->valid = FALSE;
      return NULL;
    }
    else
    {
      push_symbol_path(dst, sl_node_get_name(seg));
    }
  }

  return dst;
}

static SymbolPath *
extract_use(struct ValidationState *state, const sl_ASTNode *use)
{
  if (sl_node_get_type(use) != sl_ASTNodeType_Use)
  {
    add_error(state->unit, sl_node_get_location(use),
      "expected a use but found the wrong type of node.");
    state->valid = FALSE;
    return NULL;
  }

  if (sl_node_get_child_count(use) != 1)
  {
    add_error(state->unit, sl_node_get_location(use),
      "a use node must have a single child, containing a path");
    state->valid = FALSE;
  }

  const sl_ASTNode *path = sl_node_get_child(use, 0);

  return extract_path(state, path);
}

static int
validate_type(struct ValidationState *state,
  const sl_ASTNode *type)
{
  if (sl_node_get_type(type) != sl_ASTNodeType_Type)
  {
    add_error(state->unit, sl_node_get_location(type),
      "expected a type declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  struct PrototypeType proto;

  proto.type_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.type_path, sl_node_get_typename(type));

  proto.atomic = sl_node_get_atomic(type);

  LogicError err = add_type(state->logic, proto);
  if (err == LogicErrorSymbolAlreadyExists)
  {
    add_error(state->unit, sl_node_get_location(type),
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
  const sl_ASTNode *value, const struct TheoremEnvironment *env)
{
  if (sl_node_get_type(value) == sl_ASTNodeType_Composition)
  {
    /* Locate the corresponding expression, and verify that the types of
       the arguments match. */
    if (sl_node_get_child_count(value) != 2)
    {
      add_error(state->unit, sl_node_get_location(value),
        "a composition node must have two children, the path to the expression and a list of arguments.");
      state->valid = FALSE;
    }

    const sl_ASTNode *expr = sl_node_get_child(value, 0);
    const sl_ASTNode *args_node = sl_node_get_child(value, 1);

    SymbolPath *local_path = extract_path(state, expr);
    SymbolPath *expr_path = lookup_symbol(state, local_path);
    free_symbol_path(local_path);

    if (sl_node_get_type(args_node) != sl_ASTNodeType_CompositionArgumentList)
    {
      add_error(state->unit, sl_node_get_location(args_node),
        "expected a composition arguments node, but found the wrong type of node.");
      state->valid = FALSE;
    }
    Value **args =
      malloc(sizeof(Value *) * (sl_node_get_child_count(args_node) + 1));
    for (size_t i = 0; i < sl_node_get_child_count(args_node); ++i)
    {
      const sl_ASTNode *child = sl_node_get_child(args_node, i);
      args[i] = extract_value(state, child, env);
      if (args[i] == NULL)
      {
        /* TODO: free. */
        return NULL;
      }
    }
    args[sl_node_get_child_count(args_node)] = NULL;

    Value *v = new_composition_value(state->logic, expr_path, args);

    for (size_t i = 0; i < sl_node_get_child_count(args_node); ++i)
    {
      free_value(args[i]);
    }
    free_symbol_path(expr_path);
    free(args);

    return v;
  }
  else if (sl_node_get_type(value) == sl_ASTNodeType_Constant)
  {
    if (sl_node_get_child_count(value) != 1)
    {
      add_error(state->unit, sl_node_get_location(value),
        "a constant node must have a single child, the path to the constant.");
      state->valid = FALSE;
    }

    const sl_ASTNode *path = sl_node_get_child(value, 0);

    SymbolPath *local_path = extract_path(state, path);
    SymbolPath *const_path = lookup_symbol(state, local_path);
    free_symbol_path(local_path);

    Value *v = new_constant_value(state->logic, const_path);

    free_symbol_path(const_path);

    return v;
  }
  else if (sl_node_get_type(value) == sl_ASTNodeType_Variable)
  {
    /* Check that this corresponds to a parameter, and copy the corresponding
       type. */
    const struct PrototypeParameter *param = NULL;
    for (size_t i = 0; i < ARRAY_LENGTH(env->parameters); ++i)
    {
      const struct PrototypeParameter *p =
        ARRAY_GET(env->parameters, struct PrototypeParameter, i);
      if (strcmp(p->name, sl_node_get_name(value)) == 0)
      {
        param = p;
        break;
      }
    }

    if (param == NULL)
    {
      add_error(state->unit, sl_node_get_location(value),
        "variable does not correspond to any parameter.");
      state->valid = FALSE;
      return NULL;
    }

    return new_variable_value(state->logic, param->name, param->type);
  }
  else if (sl_node_get_type(value) == sl_ASTNodeType_Placeholder)
  {
    /* Look up the corresponding definition. */
    const struct Definition *def = NULL;
    for (size_t i = 0; i < ARRAY_LENGTH(env->definitions); ++i)
    {
      const struct Definition *d =
        ARRAY_GET(env->definitions, struct Definition, i);
      if (strcmp(d->name, sl_node_get_name(value)) == 0)
      {
        def = d;
        break;
      }
    }

    if (def == NULL)
    {
      add_error(state->unit, sl_node_get_location(value),
        "placeholder does not correspond to any definition.");
      state->valid = FALSE;
      return NULL;
    }

    return copy_value(def->value);
  }
  else
  {
    add_error(state->unit, sl_node_get_location(value),
      "expected a composition, constant, variable, or placeholder but found the wrong type of node.");
    state->valid = FALSE;
    return NULL;
  }
}

static int
extract_latex_format(struct ValidationState *state,
  const sl_ASTNode *latex, struct TheoremEnvironment *env,
  struct PrototypeLatexFormat *dst)
{
  if (sl_node_get_type(latex) != sl_ASTNodeType_Latex)
  {
    add_error(state->unit, sl_node_get_location(latex),
      "expected a latex format but found the wrong type of node.");
    state->valid = FALSE;
  }

  dst->segments = malloc(sizeof(struct PrototypeLatexFormatSegment *)
    * (sl_node_get_child_count(latex) + 1));
  for (size_t i = 0; i < sl_node_get_child_count(latex); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(latex, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_LatexString)
    {
      struct PrototypeLatexFormatSegment *seg =
        malloc(sizeof(struct PrototypeLatexFormatSegment));
      seg->is_variable = FALSE;
      seg->string = strdup(sl_node_get_name(child));
      dst->segments[i] = seg;
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_LatexVariable)
    {
      /* Attempt to extract a value from this. */
      struct PrototypeLatexFormatSegment *seg =
        malloc(sizeof(struct PrototypeLatexFormatSegment));
      seg->is_variable = TRUE;
      seg->string = strdup(sl_node_get_name(child));
      dst->segments[i] = seg;
    }
  }
  dst->segments[sl_node_get_child_count(latex)] = NULL;

  return 0;
}

static int
validate_constant(struct ValidationState *state, const sl_ASTNode *constant)
{
  if (sl_node_get_type(constant) != sl_ASTNodeType_ConstantDeclaration)
  {
    add_error(state->unit, sl_node_get_location(constant),
      "expected a constant declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  struct PrototypeConstant proto;

  proto.constant_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.constant_path, sl_node_get_name(constant));

  if (sl_node_get_child_count(constant) < 1)
  {
    add_error(state->unit, sl_node_get_location(constant),
      "a constant node must have at least a single child, containing the path to the constant's type");
    state->valid = FALSE;
  }
  const sl_ASTNode *type = sl_node_get_child(constant, 0);

  SymbolPath *local_path = extract_path(state, type);

  proto.type_path = lookup_symbol(state, local_path);
  free_symbol_path(local_path);
  proto.latex.segments = NULL;

  /* Look for latex. */
  struct TheoremEnvironment env;
  init_theorem_environment(&env);
  for (size_t i = 0; i < sl_node_get_child_count(constant); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(constant, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Latex)
    {
      int err = extract_latex_format(state, child, &env, &proto.latex);
      PROPAGATE_ERROR(err);
    }
  }
  free_theorem_environment(&env);

  LogicError err = add_constant(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, sl_node_get_location(constant),
      "cannot add constant.");
    state->valid = FALSE;
  }

  free_symbol_path(proto.constant_path);
  free_symbol_path(proto.type_path);

  return 0;
}

static int
extract_parameter(struct ValidationState *state,
  const sl_ASTNode *parameter, struct PrototypeParameter *dst)
{
  if (sl_node_get_type(parameter) != sl_ASTNodeType_Parameter)
  {
    add_error(state->unit, sl_node_get_location(parameter),
      "expected a parameter but found the wrong type of node.");
    state->valid = FALSE;
  }
  dst->name = strdup(sl_node_get_name(parameter));

  if (sl_node_get_child_count(parameter) != 1)
  {
    add_error(state->unit, sl_node_get_location(parameter),
      "a parameter node must have a single child, containing the path to the parameter's type");
    state->valid = FALSE;
  }
  const sl_ASTNode *type = sl_node_get_child(parameter, 0);

  SymbolPath *local_path = extract_path(state, type);

  dst->type = lookup_symbol(state, local_path);
  free_symbol_path(local_path);

  return 0;
}

static int
validate_expression(struct ValidationState *state,
  const sl_ASTNode *expression)
{
  if (sl_node_get_type(expression) != sl_ASTNodeType_Expression)
  {
    add_error(state->unit, sl_node_get_location(expression),
      "expected an expression declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  /* Construct a prototype expression, then try adding it to the logical
     state. */
  struct PrototypeExpression proto;
  proto.expression_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.expression_path, sl_node_get_name(expression));

  if (sl_node_get_child_count(expression) < 2)
  {
    add_error(state->unit, sl_node_get_location(expression),
      "an expression node must have at least two children, the path to the expression's type and the list of parameters.");
    state->valid = FALSE;
  }
  const sl_ASTNode *type = sl_node_get_child(expression, 0);

  SymbolPath *local_path = extract_path(state, type);
  proto.expression_type = lookup_symbol(state, local_path);
  free_symbol_path(local_path);

  /* TODO: This should be its own function. */
  struct TheoremEnvironment env;
  init_theorem_environment(&env);

  const sl_ASTNode *param_list = sl_node_get_child(expression, 1);
  if (sl_node_get_type(param_list) != sl_ASTNodeType_ParameterList)
  {
    add_error(state->unit, sl_node_get_location(param_list),
      "expected a parameter list but found the wrong type of node.");
    state->valid = FALSE;
  }

  size_t args_n = sl_node_get_child_count(param_list);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const sl_ASTNode *param = sl_node_get_child(param_list, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    ARRAY_APPEND(env.parameters, struct PrototypeParameter,
      *proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  /* If there are bindings, extract them. */
  size_t binds_n = 0;
  for (size_t i = 0; i < sl_node_get_child_count(expression); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(expression, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Bind)
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
    for (size_t i = 0; i < sl_node_get_child_count(expression); ++i)
    {
      const sl_ASTNode *child = sl_node_get_child(expression, i);
      if (sl_node_get_type(child) == sl_ASTNodeType_Bind)
      {
        const sl_ASTNode *binding = sl_node_get_child(child, 0);
        proto.bindings[binding_index] = extract_value(state, binding, &env);
        ++binding_index;
      }
    }
    proto.bindings[binds_n] = NULL;
  }

  /* Look for latex. */
  proto.latex.segments = NULL;
  for (size_t i = 0; i < sl_node_get_child_count(expression); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(expression, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Latex)
    {
      int err = extract_latex_format(state, child, &env, &proto.latex);
      PROPAGATE_ERROR(err);
    }
  }

  LogicError err = add_expression(state->logic, proto);
  if (err != LogicErrorNone)
  {
    add_error(state->unit, sl_node_get_location(expression),
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
  const sl_ASTNode *require, struct TheoremEnvironment *env)
{
  struct PrototypeRequirement *dst =
    malloc(sizeof(struct PrototypeRequirement));
  if (sl_node_get_type(require) != sl_ASTNodeType_Require)
  {
    add_error(state->unit, sl_node_get_location(require),
      "expected a requirement but found the wrong type of node.");
    state->valid = FALSE;
  }

  dst->require = strdup(sl_node_get_name(require));
  dst->arguments =
    malloc(sizeof(Value *) * (sl_node_get_child_count(require) + 1));

  for (size_t i = 0; i < sl_node_get_child_count(require); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(require, i);
    dst->arguments[i] = extract_value(state, child, env);
  }

  dst->arguments[sl_node_get_child_count(require)] = NULL;

  return dst;
}

static int
extract_definition(struct ValidationState *state,
  const sl_ASTNode *definition, struct TheoremEnvironment *env)
{
  if (sl_node_get_type(definition) != sl_ASTNodeType_Def)
  {
    add_error(state->unit, sl_node_get_location(definition),
      "expected a definition but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (sl_node_get_child_count(definition) != 1)
  {
    add_error(state->unit, sl_node_get_location(definition),
      "expected a single child of the definition node to contain the value.");
    state->valid = FALSE;
  }

  const sl_ASTNode *value_node = sl_node_get_child(definition, 0);

  struct Definition def;
  def.name = strdup(sl_node_get_name(definition));
  def.value = extract_value(state, value_node, env);

  if (def.value == NULL)
    return 1;

  ARRAY_APPEND(env->definitions, struct Definition, def);

  return 0;
}

static Value *
extract_assumption(struct ValidationState *state,
  const sl_ASTNode *assumption, struct TheoremEnvironment *env)
{
  if (sl_node_get_type(assumption) != sl_ASTNodeType_Assume)
  {
    add_error(state->unit, sl_node_get_location(assumption),
      "expected an assumption declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (sl_node_get_child_count(assumption) != 1)
  {
    add_error(state->unit, sl_node_get_location(assumption),
      "expected a single child of the assumption node to contain the value.");
    state->valid = FALSE;
  }

  const sl_ASTNode *value_node = sl_node_get_child(assumption, 0);
  return extract_value(state, value_node, env);
}

static Value *
extract_inference(struct ValidationState *state,
  const sl_ASTNode *inference, struct TheoremEnvironment *env)
{
  if (sl_node_get_type(inference) != sl_ASTNodeType_Infer)
  {
    add_error(state->unit, sl_node_get_location(inference),
      "expected an inference declaration but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (sl_node_get_child_count(inference) != 1)
  {
    add_error(state->unit, sl_node_get_location(inference),
      "expected a single child of the inference node to contain the value.");
    state->valid = FALSE;
  }

  const sl_ASTNode *value_node = sl_node_get_child(inference, 0);
  return extract_value(state, value_node, env);
}

static int
validate_axiom(struct ValidationState *state,
  const sl_ASTNode *axiom)
{
  if (sl_node_get_type(axiom) != sl_ASTNodeType_Axiom)
  {
    add_error(state->unit, sl_node_get_location(axiom),
      "expected an axiom statement but found the wrong type of node.");
    state->valid = FALSE;
  }

  /* Construct a prototype theorem, then try adding it to the logical
     state. */
  struct PrototypeTheorem proto;
  proto.theorem_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.theorem_path, sl_node_get_name(axiom));

  size_t requirements_n = 0;
  size_t assumptions_n = 0;
  size_t inferences_n = 0;
  for (size_t i = 0; i < sl_node_get_child_count(axiom); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(axiom, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Require)
      ++requirements_n;
    else if (sl_node_get_type(child) == sl_ASTNodeType_Assume)
      ++assumptions_n;
    else if (sl_node_get_type(child) == sl_ASTNodeType_Infer)
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

  const sl_ASTNode *param_list = sl_node_get_child(axiom, 0);
  if (sl_node_get_type(param_list) != sl_ASTNodeType_ParameterList)
  {
    add_error(state->unit, sl_node_get_location(param_list),
      "expected a parameter list but found the wrong type of node.");
    state->valid = FALSE;
  }

  size_t args_n = sl_node_get_child_count(param_list);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const sl_ASTNode *param = sl_node_get_child(param_list, i);
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
  for (size_t i = 0; i < sl_node_get_child_count(axiom); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(axiom, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Require)
    {
      proto.requirements[require_index] = extract_require(state, child, &env);
      ++require_index;
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Def)
    {
      int err = extract_definition(state, child, &env);
      PROPAGATE_ERROR(err);
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Assume)
    {
      proto.assumptions[assume_index] = extract_assumption(state, child, &env);
      ++assume_index;
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Infer)
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
    add_error(state->unit, sl_node_get_location(axiom),
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
extract_step(struct ValidationState *state, const sl_ASTNode *step,
  struct TheoremEnvironment *env)
{
  struct PrototypeProofStep *dst = malloc(sizeof(struct PrototypeProofStep));

  /* Find the theorem that is being referenced here. */
  if (sl_node_get_type(step) != sl_ASTNodeType_Step)
  {
    add_error(state->unit, sl_node_get_location(step),
      "expected a proof step but found the wrong type of node.");
    state->valid = FALSE;
  }
  if (sl_node_get_child_count(step) != 1)
  {
    add_error(state->unit, sl_node_get_location(step),
      "a step node must have exactly one child, the theorem reference.");
    state->valid = FALSE;
  }

  const sl_ASTNode *thm_ref = sl_node_get_child(step, 0);
  if (sl_node_get_type(thm_ref) != sl_ASTNodeType_TheoremReference)
  {
    add_error(state->unit, sl_node_get_location(thm_ref),
      "expected a theorem reference but found the wrong type of node.");
    state->valid = FALSE;
  }
  if (sl_node_get_child_count(thm_ref) == 0)
  {
    add_error(state->unit, sl_node_get_location(thm_ref),
      "a theorem reference must have at least one child, the path to the theorem.");
    state->valid = FALSE;
  }

  const sl_ASTNode *thm_path_node = sl_node_get_child(thm_ref, 0);
  SymbolPath *local_path = extract_path(state, thm_path_node);
  dst->theorem_path = lookup_symbol(state, local_path);
  free_symbol_path(local_path);
  dst->arguments = malloc(sizeof(Value *) * (sl_node_get_child_count(thm_ref)));

  /* Next, extract all the arguments being passed to the theorem. */
  for (size_t i = 0; i < sl_node_get_child_count(thm_ref) - 1; ++i)
  {
    const sl_ASTNode *arg = sl_node_get_child(thm_ref, i + 1);
    dst->arguments[i] = extract_value(state, arg, env);
  }
  dst->arguments[sl_node_get_child_count(thm_ref) - 1] = NULL;

  return dst;
}

static int
validate_theorem(struct ValidationState *state,
  const sl_ASTNode *theorem)
{
  if (sl_node_get_type(theorem) != sl_ASTNodeType_Theorem)
  {
    add_error(state->unit, sl_node_get_location(theorem),
      "expected a theorem statement but found the wrong type of node.");
    state->valid = FALSE;
  }

  /* Construct a prototype theorem, then try adding it to the logical
     state. */
  struct PrototypeTheorem proto;
  proto.theorem_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.theorem_path, sl_node_get_name(theorem));

  size_t requirements_n = 0;
  size_t assumptions_n = 0;
  size_t inferences_n = 0;
  size_t steps_n = 0;
  for (size_t i = 0; i < sl_node_get_child_count(theorem); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(theorem, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Require)
      ++requirements_n;
    if (sl_node_get_type(child) == sl_ASTNodeType_Assume)
      ++assumptions_n;
    else if (sl_node_get_type(child) == sl_ASTNodeType_Infer)
      ++inferences_n;
    else if (sl_node_get_type(child) == sl_ASTNodeType_Step)
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

  const sl_ASTNode *param_list = sl_node_get_child(theorem, 0);
  if (sl_node_get_type(param_list) != sl_ASTNodeType_ParameterList)
  {
    add_error(state->unit, sl_node_get_location(param_list),
      "expected a parameter list but found the wrong type of node.");
    state->valid = FALSE;
  }

  size_t args_n = sl_node_get_child_count(param_list);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const sl_ASTNode *param = sl_node_get_child(param_list, i);
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
  for (size_t i = 0; i < sl_node_get_child_count(theorem); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(theorem, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_Require)
    {
      proto.requirements[require_index] = extract_require(state, child, &env);
      ++require_index;
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Def)
    {
      int err = extract_definition(state, child, &env);
      PROPAGATE_ERROR(err);
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Assume)
    {
      proto.assumptions[assume_index] = extract_assumption(state, child, &env);
      char *str = string_from_value(proto.assumptions[assume_index]);
      free(str);
      ++assume_index;
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Infer)
    {
      proto.inferences[infer_index] = extract_inference(state, child, &env);
      ++infer_index;
    }
    else if (sl_node_get_type(child) == sl_ASTNodeType_Step)
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
    add_error(state->unit, sl_node_get_location(theorem),
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
  const sl_ASTNode *namespace)
{
  if (sl_node_get_type(namespace) != sl_ASTNodeType_Namespace)
  {
    add_error(state->unit, sl_node_get_location(namespace),
      "expected a namespace but found the wrong type of node.");
    state->valid = FALSE;
  }

  if (sl_node_get_name(namespace) != NULL)
  {
    push_symbol_path(state->prefix_path, sl_node_get_name(namespace));
  }

  SymbolPath *search_path = copy_symbol_path(state->prefix_path);
  ARRAY_APPEND(state->search_paths, SymbolPath *, search_path);

  /* Validate all the objects contained in this namespace. */
  Array using_paths;
  ARRAY_INIT(using_paths, SymbolPath *);
  for (size_t i = 0; i < sl_node_get_child_count(namespace); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(namespace, i);
    int err;
    switch (sl_node_get_type(child))
    {
      case sl_ASTNodeType_Namespace:
        err = validate_namespace(state, child);
        PROPAGATE_ERROR(err);
        break;
      case sl_ASTNodeType_Use:
        {
          SymbolPath *use_path = extract_use(state, child);
          ARRAY_APPEND(using_paths, SymbolPath *, use_path);
          ARRAY_APPEND(state->search_paths, SymbolPath *, use_path);
        }
        break;
      case sl_ASTNodeType_Type:
        err = validate_type(state, child);
        PROPAGATE_ERROR(err);
        break;
      case sl_ASTNodeType_ConstantDeclaration:
        err = validate_constant(state, child);
        PROPAGATE_ERROR(err);
        break;
      case sl_ASTNodeType_Expression:
        err = validate_expression(state, child);
        PROPAGATE_ERROR(err);
        break;
      case sl_ASTNodeType_Axiom:
        err = validate_axiom(state, child);
        PROPAGATE_ERROR(err);
        break;
      case sl_ASTNodeType_Theorem:
        err = validate_theorem(state, child);
        PROPAGATE_ERROR(err);
        break;
      default:
        add_error(state->unit, sl_node_get_location(child),
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

  if (sl_node_get_name(namespace) != NULL)
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
  const sl_ASTNode *root_node = state->input->ast_root;
  if (sl_node_get_child_count(root_node) == 0)
  {
    add_error(state->unit, NULL,
      "No root namespace provided.");
    state->valid = FALSE;
    return 1;
  }

  const sl_ASTNode *root_namespace = sl_node_get_child(root_node, 0);
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
  free_tree(parse_out.ast_root);
  PROPAGATE_ERROR(err);

  free_lex_state(&lex_out);
  close_compilation_unit(&unit);

  return 0;
}
