#include "logic.h"
#include "parse.h"
#include <string.h>

#if defined(__APPLE__) || defined(__linux__)
#include <stdlib.h>
#include <libgen.h>
#include <limits.h>
#endif

struct ValidationState
{
  bool valid;

  char *prefix;
  ARR(char *) files_opened;
  sl_TextInput *text;
  sl_LogicState *logic;
  sl_SymbolPath *prefix_path;
  ARR(sl_SymbolPath *) search_paths;
};

static int
validate_import(struct ValidationState *state, const sl_ASTNode *import);

static sl_SymbolPath *
lookup_symbol(struct ValidationState *state, const sl_SymbolPath *path)
{
  /* Build a list of candidate absolute paths. */
  sl_SymbolPath **paths = malloc(sizeof(sl_SymbolPath *) *
    (ARRAY_LENGTH(state->search_paths) + 1));
  for (size_t i = 0; i < ARRAY_LENGTH(state->search_paths); ++i)
  {
    const sl_SymbolPath *search_in =
      *ARRAY_GET(state->search_paths, sl_SymbolPath *, i);
    paths[i] = copy_symbol_path(search_in);
    append_symbol_path(paths[i], path);
  }
  paths[ARRAY_LENGTH(state->search_paths)] = NULL;

  sl_SymbolPath *result = find_first_occupied_path(state->logic, paths);

  for (size_t i = 0; i < ARRAY_LENGTH(state->search_paths); ++i)
    free_symbol_path(paths[i]);
  free(paths);

  return result;
}

static sl_SymbolPath *
extract_path(struct ValidationState *state, const sl_ASTNode *path)
{
  if (sl_node_get_type(path) != sl_ASTNodeType_Path)
  {
    sl_node_show_message(state->text, path,
      "expected a path but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  sl_SymbolPath *dst = init_symbol_path();
  for (size_t i = 0; i < sl_node_get_child_count(path); ++i)
  {
    const sl_ASTNode *seg = sl_node_get_child(path, i);
    if (sl_node_get_type(seg) != sl_ASTNodeType_PathSegment)
    {
      sl_node_show_message(state->text, seg,
        "expected a path segment but found the wrong type of node.",
        sl_MessageType_Error);
      state->valid = FALSE;
      free_symbol_path(dst);
      return NULL;
    }
    else
    {
      push_symbol_path(dst, sl_node_get_name(seg));
    }
  }

  return dst;
}

static sl_SymbolPath *
extract_use(struct ValidationState *state, const sl_ASTNode *use)
{
  if (sl_node_get_type(use) != sl_ASTNodeType_Use)
  {
    sl_node_show_message(state->text, use,
      "expected a use but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  if (sl_node_get_child_count(use) != 1)
  {
    sl_node_show_message(state->text, use,
      "a use node must have a single child, containing a path.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  const sl_ASTNode *path = sl_node_get_child(use, 0);

  return extract_path(state, path);
}

static int
validate_type(struct ValidationState *state,
  const sl_ASTNode *type)
{
  struct PrototypeType proto;
  LogicError err;

  if (sl_node_get_type(type) != sl_ASTNodeType_Type)
  {
    sl_node_show_message(state->text, type,
      "expected a type declaration but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }
  proto.type_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.type_path, sl_node_get_name(type));

  proto.atomic = FALSE;
  proto.binds = FALSE;
  for (size_t i = 0; i < sl_node_get_child_count(type); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(type, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_AtomicFlag)
      proto.atomic = TRUE;
    else if (sl_node_get_type(child) == sl_ASTNodeType_BindsFlag)
      proto.binds = TRUE;
  }

  err = add_type(state->logic, proto);
  if (err == LogicErrorSymbolAlreadyExists)
  {
    sl_node_show_message(state->text, type,
      "symbol already exists when declaring type.",
      sl_MessageType_Error);
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
  ARR(struct PrototypeParameter) parameters;
  ARR(struct Definition) definitions;
};

static void
init_theorem_environment(struct TheoremEnvironment *thm)
{
  ARR_INIT(thm->parameters);
  ARR_INIT(thm->definitions);
}

static void
free_theorem_environment(struct TheoremEnvironment *thm)
{
  ARR_FREE(thm->parameters);
  for (size_t i = 0; i < ARR_LENGTH(thm->definitions); ++i)
  {
    struct Definition *def = ARR_GET(thm->definitions, i);
    free_definition(def);
  }
  ARR_FREE(thm->definitions);
}

static Value *
extract_value(struct ValidationState *state,
  const sl_ASTNode *value, const struct TheoremEnvironment *env)
{
  if (sl_node_get_type(value) == sl_ASTNodeType_Composition)
  {
    /* Locate the corresponding expression, and verify that the types of
       the arguments match. */
    const sl_ASTNode *expr, *args_node;
    sl_SymbolPath *expr_path;
    Value *v;
    if (sl_node_get_child_count(value) != 2)
    {
      sl_node_show_message(state->text, value,
        "a composition node must have two children, the path to the expression and a list of arguments.",
        sl_MessageType_Error);
      state->valid = FALSE;
      return NULL;
    }

    expr = sl_node_get_child(value, 0);
    args_node = sl_node_get_child(value, 1);
    {
      sl_SymbolPath *local_path = extract_path(state, expr);
      expr_path = lookup_symbol(state, local_path);
      free_symbol_path(local_path);
    }

    if (sl_node_get_type(args_node) != sl_ASTNodeType_ArgumentList)
    {
      sl_node_show_message(state->text, args_node,
        "expected a composition arguments node, but found the wrong type of node.",
        sl_MessageType_Error);
      state->valid = FALSE;
      free_symbol_path(expr_path);
      return NULL;
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

    v = new_composition_value(state->logic, expr_path, args);

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
    const sl_ASTNode *path;
    sl_SymbolPath *const_path;
    Value *v;
    if (sl_node_get_child_count(value) != 1)
    {
      sl_node_show_message(state->text, value,
        "a constant node must have a single child, the path to the constant.",
        sl_MessageType_Error);
      state->valid = FALSE;
      return NULL;
    }

    path = sl_node_get_child(value, 0);
    {
      sl_SymbolPath *local_path = extract_path(state, path);
      const_path = lookup_symbol(state, local_path);
      free_symbol_path(local_path);
    }

    v = new_constant_value(state->logic, const_path);
    free_symbol_path(const_path);

    return v;
  }
  else if (sl_node_get_type(value) == sl_ASTNodeType_Variable)
  {
    /* Check that this corresponds to a parameter, and copy the corresponding
       type. */
    const struct PrototypeParameter *param = NULL;
    for (size_t i = 0; i < ARR_LENGTH(env->parameters); ++i)
    {
      const struct PrototypeParameter *p = ARR_GET(env->parameters, i);
      if (strcmp(p->name, sl_node_get_name(value)) == 0)
      {
        param = p;
        break;
      }
    }

    if (param == NULL)
    {
      sl_node_show_message(state->text, value,
        "variable does not correspond to any parameter.",
        sl_MessageType_Error);
      state->valid = FALSE;
      return NULL;
    }

    return new_variable_value(state->logic, param->name, param->type);
  }
  else if (sl_node_get_type(value) == sl_ASTNodeType_Placeholder)
  {
    /* Look up the corresponding definition. */
    const struct Definition *def = NULL;
    for (size_t i = 0; i < ARR_LENGTH(env->definitions); ++i)
    {
      const struct Definition *d = ARR_GET(env->definitions, i);
      if (strcmp(d->name, sl_node_get_name(value)) == 0)
      {
        def = d;
        break;
      }
    }

    if (def == NULL)
    {
      sl_node_show_message(state->text, value,
        "placeholder does not correspond to any definition.",
        sl_MessageType_Error);
      state->valid = FALSE;
      return NULL;
    }

    return copy_value(def->value);
  }
  else
  {
    sl_node_show_message(state->text, value,
      "expected a composition, constant, variable, or placeholder but found the wrong type of node.",
      sl_MessageType_Error);
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
    sl_node_show_message(state->text, latex,
      "expected a latex format but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
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
  struct PrototypeConstant proto;
  const sl_ASTNode *type;
  struct TheoremEnvironment env;
  LogicError err;
  if (sl_node_get_type(constant) != sl_ASTNodeType_ConstantDeclaration)
  {
    sl_node_show_message(state->text, constant,
      "expected a constant declaration but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  proto.constant_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.constant_path, sl_node_get_name(constant));

  if (sl_node_get_child_count(constant) < 1)
  {
    sl_node_show_message(state->text, constant,
      "a constant node must have at least a single child, containing the path to the constant's type",
      sl_MessageType_Error);
    state->valid = FALSE;
    free(proto.constant_path);
    return 0;
  }
  type = sl_node_get_child(constant, 0);

  {
    sl_SymbolPath *local_path = extract_path(state, type);
    proto.type_path = lookup_symbol(state, local_path);
    free_symbol_path(local_path);
  }

  /* Look for latex. */
  proto.latex.segments = NULL;
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

  err = add_constant(state->logic, proto);
  if (err != LogicErrorNone)
  {
    sl_node_show_message(state->text, constant,
      "cannot add constant.",
      sl_MessageType_Error);
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
  const sl_ASTNode *type;
  if (sl_node_get_type(parameter) != sl_ASTNodeType_Parameter)
  {
    sl_node_show_message(state->text, parameter,
      "expected a parameter but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }
  dst->name = strdup(sl_node_get_name(parameter));

  if (sl_node_get_child_count(parameter) != 1)
  {
    sl_node_show_message(state->text, parameter,
      "a parameter node must have a single child, containing the path to the parameter's type",
      sl_MessageType_Error);
    state->valid = FALSE;
    free(dst->name);
    return 0;
  }
  type = sl_node_get_child(parameter, 0);

  {
    sl_SymbolPath *local_path = extract_path(state, type);
    dst->type = lookup_symbol(state, local_path);
    free_symbol_path(local_path);
  }
  return 0;
}

static int
validate_expression(struct ValidationState *state,
  const sl_ASTNode *expression)
{
  struct PrototypeExpression proto;
  const sl_ASTNode *type, *param_list;
  struct TheoremEnvironment env;
  size_t args_n, binds_n;
  LogicError err;
  if (sl_node_get_type(expression) != sl_ASTNodeType_Expression)
  {
    sl_node_show_message(state->text, expression,
      "expected an expression declaration but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  /* Construct a prototype expression, then try adding it to the logical
     state. */
  proto.expression_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.expression_path, sl_node_get_name(expression));
  if (sl_node_get_child_count(expression) < 2)
  {
    sl_node_show_message(state->text, expression,
      "an expression node must have at least two children, the path to the expression's type and the list of parameters.",
      sl_MessageType_Error);
    state->valid = FALSE;
    free_symbol_path(proto.expression_path);
    return 0;
  }
  type = sl_node_get_child(expression, 0);

  {
    sl_SymbolPath *local_path = extract_path(state, type);
    proto.expression_type = lookup_symbol(state, local_path);
    free_symbol_path(local_path);
  }

  /* TODO: This should be its own function. */
  init_theorem_environment(&env);
  param_list = sl_node_get_child(expression, 1);
  if (sl_node_get_type(param_list) != sl_ASTNodeType_ParameterList)
  {
    sl_node_show_message(state->text, param_list,
      "expected a parameter list but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    free_symbol_path(proto.expression_path);
    free_symbol_path(proto.expression_type);
    return 0;
  }

  args_n = sl_node_get_child_count(param_list);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const sl_ASTNode *param = sl_node_get_child(param_list, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    ARR_APPEND(env.parameters, *proto.parameters[i]);
    PROPAGATE_ERROR(err); /* TODO: free in case of error. */
  }
  proto.parameters[args_n] = NULL;

  /* If there are bindings, extract them. */
  binds_n = 0;
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

  /* Is this expression atomic, or defined in terms of another expression? */
  proto.replace_with = NULL;
  for (size_t i = 0; i < sl_node_get_child_count(expression); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(expression, i);
    if (sl_node_get_type(child) == sl_ASTNodeType_ExpressionAs)
    {
      if (sl_node_get_child_count(child) != 1)
      {
        sl_node_show_message(state->text, child,
          "Expression 'as' node should have a single child, the value it abbreviates.",
          sl_MessageType_Error);
        state->valid = FALSE;
      }

      proto.replace_with =
        extract_value(state, sl_node_get_child(child, 0), &env);
    }
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

  err = add_expression(state->logic, proto);
  if (err != LogicErrorNone)
  {
    sl_node_show_message(state->text, expression,
      "cannot add expression to logic state.",
      sl_MessageType_Error);
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
  const sl_ASTNode *args;
  if (sl_node_get_type(require) != sl_ASTNodeType_Require)
  {
    sl_node_show_message(state->text, require,
      "expected a requirement but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    free(dst);
    return NULL;
  }
  if (sl_node_get_child_count(require) != 1)
  {
    sl_node_show_message(state->text, require,
      "a requirement node should have exactly one child, its list of arguments.",
      sl_MessageType_Error);
    state->valid = FALSE;
    free(dst);
    return NULL;
  }

  dst->require = strdup(sl_node_get_name(require));
  args = sl_node_get_child(require, 0);
  dst->arguments =
    malloc(sizeof(Value *) * (sl_node_get_child_count(args) + 1));
  for (size_t i = 0; i < sl_node_get_child_count(args); ++i)
  {
    const sl_ASTNode *child = sl_node_get_child(args, i);
    dst->arguments[i] = extract_value(state, child, env);
  }
  dst->arguments[sl_node_get_child_count(args)] = NULL;

  return dst;
}

static int
extract_definition(struct ValidationState *state,
  const sl_ASTNode *definition, struct TheoremEnvironment *env)
{
  const sl_ASTNode *value_node;
  struct Definition def;
  if (sl_node_get_type(definition) != sl_ASTNodeType_Def)
  {
    sl_node_show_message(state->text, definition,
      "expected a definition but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  if (sl_node_get_child_count(definition) != 1)
  {
    sl_node_show_message(state->text, definition,
      "expected a single child of the definition node to contain the value.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  value_node = sl_node_get_child(definition, 0);
  def.name = strdup(sl_node_get_name(definition));
  def.value = extract_value(state, value_node, env);
  if (def.value == NULL)
  {
    free(def.name);
    return 1;
  }

  ARR_APPEND(env->definitions, def);

  return 0;
}

static Value *
extract_assumption(struct ValidationState *state,
  const sl_ASTNode *assumption, struct TheoremEnvironment *env)
{
  const sl_ASTNode *value_node;
  if (sl_node_get_type(assumption) != sl_ASTNodeType_Assume)
  {
    sl_node_show_message(state->text, assumption,
      "expected an assumption declaration but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  if (sl_node_get_child_count(assumption) != 1)
  {
    sl_node_show_message(state->text, assumption,
      "expected a single child of the assumption node to contain the value.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  value_node = sl_node_get_child(assumption, 0);
  return extract_value(state, value_node, env);
}

static Value *
extract_inference(struct ValidationState *state,
  const sl_ASTNode *inference, struct TheoremEnvironment *env)
{
  const sl_ASTNode *value_node;
  if (sl_node_get_type(inference) != sl_ASTNodeType_Infer)
  {
    sl_node_show_message(state->text, inference,
      "expected an inference declaration but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  if (sl_node_get_child_count(inference) != 1)
  {
    sl_node_show_message(state->text, inference,
      "expected a single child of the inference node to contain the value.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  value_node = sl_node_get_child(inference, 0);
  return extract_value(state, value_node, env);
}

static int
validate_axiom(struct ValidationState *state,
  const sl_ASTNode *axiom)
{
  struct PrototypeTheorem proto;
  size_t requirements_n, assumptions_n, inferences_n, args_n;
  struct TheoremEnvironment env;
  const sl_ASTNode *param_list;
  LogicError err;
  if (sl_node_get_type(axiom) != sl_ASTNodeType_Axiom)
  {
    sl_node_show_message(state->text, axiom,
      "expected an axiom statement but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  /* Construct a prototype theorem, then try adding it to the logical
     state. */
  proto.theorem_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.theorem_path, sl_node_get_name(axiom));

  requirements_n = 0;
  assumptions_n = 0;
  inferences_n = 0;
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

  init_theorem_environment(&env);
  param_list = sl_node_get_child(axiom, 0);
  if (sl_node_get_type(param_list) != sl_ASTNodeType_ParameterList)
  {
    sl_node_show_message(state->text, param_list,
      "expected a parameter list but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    /* TODO: free. */
    return 0;
  }

  args_n = sl_node_get_child_count(param_list);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const sl_ASTNode *param = sl_node_get_child(param_list, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    ARR_APPEND(env.parameters, *proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  {
    size_t require_index, assume_index, infer_index;
    require_index = 0;
    assume_index = 0;
    infer_index = 0;
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
        proto.assumptions[assume_index] =
          extract_assumption(state, child, &env);
        ++assume_index;
      }
      else if (sl_node_get_type(child) == sl_ASTNodeType_Infer)
      {
        proto.inferences[infer_index] = extract_inference(state, child, &env);
        ++infer_index;
      }
    }
  }
  free_theorem_environment(&env);
  proto.parameters[args_n] = NULL;
  proto.requirements[requirements_n] = NULL;
  proto.assumptions[assumptions_n] = NULL;
  proto.inferences[inferences_n] = NULL;

  err = add_axiom(state->logic, proto);
  if (err != LogicErrorNone)
  {
    sl_node_show_message(state->text, axiom,
      "cannot add axiom to logic state.",
      sl_MessageType_Error);
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
  struct PrototypeProofStep *dst;
  const sl_ASTNode *thm_ref, *thm_ref_path, *arg_list;
  /* Find the theorem that is being referenced here. */
  if (sl_node_get_type(step) != sl_ASTNodeType_Step)
  {
    sl_node_show_message(state->text, step,
      "expected a proof step but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }
  if (sl_node_get_child_count(step) != 1)
  {
    sl_node_show_message(state->text, step,
      "a step node must have exactly one child, the theorem reference.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }

  thm_ref = sl_node_get_child(step, 0);
  if (sl_node_get_type(thm_ref) != sl_ASTNodeType_TheoremReference)
  {
    sl_node_show_message(state->text, thm_ref,
      "expected a theorem reference but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return NULL;
  }
  if (sl_node_get_child_count(thm_ref) < 2)
  {
    sl_node_show_message(state->text, step,
      "a theorem reference must have at least two children, the path to the theorem and the list of arguments.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  thm_ref_path = sl_node_get_child(thm_ref, 0);
  dst = SL_NEW(struct PrototypeProofStep);
  {
    sl_SymbolPath *local_path = extract_path(state, thm_ref_path);
    dst->theorem_path = lookup_symbol(state, local_path);
    free_symbol_path(local_path);
  }

  /* Next, extract all the arguments being passed to the theorem. */
  arg_list = sl_node_get_child(thm_ref, 1);
  dst->arguments = malloc(sizeof(Value *) *
    (sl_node_get_child_count(arg_list) + 1));
  if (sl_node_get_type(arg_list) != sl_ASTNodeType_ArgumentList)
  {
    sl_node_show_message(state->text, arg_list,
      "expected an argument list but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    /* TODO: free. */
    return NULL;
  }
  for (size_t i = 0; i < sl_node_get_child_count(arg_list); ++i)
  {
    const sl_ASTNode *arg = sl_node_get_child(arg_list, i);
    dst->arguments[i] = extract_value(state, arg, env);
  }
  dst->arguments[sl_node_get_child_count(arg_list)] = NULL;

  return dst;
}

static int
validate_theorem(struct ValidationState *state,
  const sl_ASTNode *theorem)
{
  struct PrototypeTheorem proto;
  size_t requirements_n, assumptions_n, inferences_n, steps_n, args_n;
  struct TheoremEnvironment env;
  const sl_ASTNode *param_list;
  LogicError err;
  if (sl_node_get_type(theorem) != sl_ASTNodeType_Theorem)
  {
    sl_node_show_message(state->text, theorem,
      "expected a theorem statement but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  /* Construct a prototype theorem, then try adding it to the logical
     state. */
  proto.theorem_path = copy_symbol_path(state->prefix_path);
  push_symbol_path(proto.theorem_path, sl_node_get_name(theorem));

  requirements_n = 0;
  assumptions_n = 0;
  inferences_n = 0;
  steps_n = 0;
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

  param_list = sl_node_get_child(theorem, 0);
  init_theorem_environment(&env);
  if (sl_node_get_type(param_list) != sl_ASTNodeType_ParameterList)
  {
    sl_node_show_message(state->text, theorem,
      "expected a parameter list but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    /* TODO: free. */
    return 0;
  }

  args_n = sl_node_get_child_count(param_list);
  proto.parameters = malloc(sizeof(struct PrototypeParameter *) * (args_n + 1));
  for (size_t i = 0; i < args_n; ++i)
  {
    const sl_ASTNode *param = sl_node_get_child(param_list, i);
    proto.parameters[i] = malloc(sizeof(struct PrototypeParameter));
    int err = extract_parameter(state, param, proto.parameters[i]);
    ARR_APPEND(env.parameters, *proto.parameters[i]);
    PROPAGATE_ERROR(err);
  }
  proto.parameters[args_n] = NULL;

  {
    size_t require_index, assume_index, infer_index, step_index;
    require_index = 0;
    assume_index = 0;
    infer_index = 0;
    step_index = 0;
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
  }
  free_theorem_environment(&env);
  proto.parameters[args_n] = NULL;
  proto.requirements[requirements_n] = NULL;
  proto.assumptions[assumptions_n] = NULL;
  proto.inferences[inferences_n] = NULL;
  proto.steps[steps_n] = NULL;

  err = add_theorem(state->logic, proto);
  if (err != LogicErrorNone)
  {
    sl_node_show_message(state->text, theorem,
      "cannot add theorem to logic state.",
      sl_MessageType_Error);
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
    sl_node_show_message(state->text, namespace,
      "expected a namespace but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  if (sl_node_get_name(namespace) != NULL)
    push_symbol_path(state->prefix_path, sl_node_get_name(namespace));

  sl_SymbolPath *search_path = copy_symbol_path(state->prefix_path);
  ARR_APPEND(state->search_paths, search_path);

  /* Validate all the objects contained in this namespace. */
  ARR(sl_SymbolPath *) using_paths;
  ARR_INIT(using_paths);
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
      case sl_ASTNodeType_Import:
        err = validate_import(state, child);
        PROPAGATE_ERROR(err);
        break;
      case sl_ASTNodeType_Use:
        {
          sl_SymbolPath *use_path = extract_use(state, child);
          ARR_APPEND(using_paths, use_path);
          ARR_APPEND(state->search_paths, use_path);
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
        sl_node_show_message(state->text, child,
          "expected a namespace, use, type, constant, expression, axiom, or theorem, but found the wrong type of node.",
          sl_MessageType_Error);
        state->valid = FALSE;
        break;
    }
  }

  for (size_t i = 0; i < ARR_LENGTH(using_paths); ++i)
  {
    sl_SymbolPath *path = *ARR_GET(using_paths, i);
    free_symbol_path(path);
    ARR_POP(state->search_paths);
  }
  ARR_FREE(using_paths);
  ARR_POP(state->search_paths);
  free_symbol_path(search_path);

  if (sl_node_get_name(namespace) != NULL)
  {
    pop_symbol_path(state->prefix_path);
  }

  return 0;
}

static int
load_file_and_validate(struct ValidationState *state, const char *path)
{
  /* TODO: check that the path is accessible and report this error. */
  sl_TextInput *input;
  sl_LexerState *lex;
  sl_ASTNode *ast;
  char *old_prefix = state->prefix;
  char *absolute_path;
  if (path == NULL)
  {
    state->valid = FALSE;
    return 0;
  }

  /* Establish the prefix path by taking the global path of the directory
     containing the target file. */
#if defined(__APPLE__) || defined(__linux__)
  if (state->prefix == NULL)
  {
    char full_path[PATH_MAX];
    if (realpath(path, full_path) == NULL)
    {
      /* TODO: error. */
      return 0;
    }
    absolute_path = strdup(full_path);
  }
  else
  {
    asprintf(&absolute_path, "%s/%s", state->prefix, path);

  }
  state->prefix = strdup(dirname(absolute_path));
#endif

  for (size_t i = 0; i < ARR_LENGTH(state->files_opened); ++i)
  {
    if (strcmp(absolute_path, *ARR_GET(state->files_opened, i)) == 0)
      return 0;
  }
  ARR_APPEND(state->files_opened, strdup(absolute_path));

  input = sl_input_from_file(absolute_path);
  if (input == NULL)
  {
    /* TODO: report error. */
    state->valid = FALSE;
    return 0;
  }

  lex = sl_lexer_new_state_with_input(input);
  if (lex == NULL)
  {
    /* TODO: report error. */
    sl_input_free(input);
    state->valid = FALSE;
    return 0;
  }

  ast = sl_parse_input(lex);
  if (ast == NULL)
  {
    /* TODO: report error. */
    sl_input_free(input);
    sl_lexer_free_state(lex);
    state->valid = FALSE;
    return 0;
  }
  //sl_print_tree(ast);

  {
    sl_TextInput *old_input = state->text;
    state->text = input;
    state->text = old_input;
  }
  int result = validate_namespace(state, ast);

  sl_input_free(input);
  sl_lexer_free_state(lex);
  sl_node_free(ast);
  free(absolute_path);
  free(state->prefix);
  state->prefix = old_prefix;

  return result;
}

static int
validate_import(struct ValidationState *state, const sl_ASTNode *import)
{
  if (sl_node_get_type(import) != sl_ASTNodeType_Import)
  {
    sl_node_show_message(state->text, import,
      "expected an import statement but found the wrong type of node.",
      sl_MessageType_Error);
    state->valid = FALSE;
    return 0;
  }

  return load_file_and_validate(state, sl_node_get_name(import));
}

int
sl_verify_and_add_file(const char *path, sl_LogicState *logic)
{
  struct ValidationState state;
  state.valid = TRUE;
  state.prefix_path = init_symbol_path();
  state.logic = logic;
  state.prefix = NULL;
  ARR_INIT(state.files_opened);
  ARR_INIT(state.search_paths);

  int err = load_file_and_validate(&state, path);

  free_symbol_path(state.prefix_path);
  ARR_FREE(state.search_paths);

  if (err != 0)
    return err;
  if (state.prefix != NULL)
    free(state.prefix);
  for (size_t i = 0; i < ARR_LENGTH(state.files_opened); ++i)
    free(*ARR_GET(state.files_opened, i));
  ARR_FREE(state.files_opened);
  return state.valid ? 0 : 1;
}
