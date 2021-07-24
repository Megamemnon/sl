#include "logic.h"
#include "sl.h"
#include <string.h>

#include "core.h"

/* Paths */
SymbolPath *
init_symbol_path()
{
  SymbolPath *path = malloc(sizeof(SymbolPath));
  ARR_INIT(path->segments);
  return path;
}

SymbolPath *
copy_symbol_path(const SymbolPath *src)
{
  SymbolPath *dst = init_symbol_path();
  for (size_t i = 0; i < ARR_LENGTH(src->segments); ++i)
  {
    ARR_APPEND(dst->segments, strdup(*ARRAY_GET(src->segments, char *, i)));
  }
  return dst;
}

void
free_symbol_path(SymbolPath *path)
{
  for (size_t i = 0; i < ARR_LENGTH(path->segments); ++i)
  {
    free(*ARR_GET(path->segments, i));
  }
  ARR_FREE(path->segments);
  free(path);
}

int
length_of_symbol_path(const SymbolPath *path)
{
  return ARR_LENGTH(path->segments);
}

const char *
get_symbol_path_segment(const SymbolPath *path, size_t index)
{
  return *ARR_GET(path->segments, index);
}

const char *
get_symbol_path_last_segment(const SymbolPath *path)
{
  return get_symbol_path_segment(path, length_of_symbol_path(path) - 1);
}

char *
string_from_symbol_path(const SymbolPath *path)
{
  if (ARR_LENGTH(path->segments) == 0)
    return strdup("");
  size_t str_len = ARR_LENGTH(path->segments);
  for (size_t i = 0; i < ARR_LENGTH(path->segments); ++i)
  {
    const char *segment = *ARR_GET(path->segments, i);
    str_len += strlen(segment);
  }
  char *str = malloc(str_len);
  char *c = str;
  for (size_t i = 0; i < ARR_LENGTH(path->segments); ++i)
  {
    if (i > 0)
    {
      *c = '.';
      ++c;
    }
    const char *segment = *ARR_GET(path->segments, i);
    strcpy(c, segment);
    c += strlen(segment);
  }
  *c = '\0';
  return str;
}

void
push_symbol_path(SymbolPath *path, const char *segment)
{
  ARR_APPEND(path->segments, strdup(segment));
}

void
pop_symbol_path(SymbolPath *path)
{
  free(*ARR_GET(path->segments, ARRAY_LENGTH(path->segments) - 1));
  ARR_POP(path->segments);
}

void
append_symbol_path(SymbolPath *path, const SymbolPath *to_append)
{
  for (size_t i = 0; i < ARR_LENGTH(to_append->segments); ++i)
  {
    const char *segment = *ARR_GET(to_append->segments, i);
    push_symbol_path(path, segment);
  }
}

bool
symbol_paths_equal(const SymbolPath *a, const SymbolPath *b)
{
  if (ARR_LENGTH(a->segments) != ARR_LENGTH(b->segments))
    return FALSE;
  for (size_t i = 0; i < ARR_LENGTH(a->segments); ++i)
  {
    const char *a_segment = *ARR_GET(a->segments, i);
    const char *b_segment = *ARR_GET(b->segments, i);
    if (strcmp(a_segment, b_segment) != 0)
      return FALSE;
  }
  return TRUE;
}

/* Parameters */
static void
free_parameter(struct Parameter *param)
{
  free(param->name);
}

/* Types */
static void
free_type(struct Type *type)
{

}

/* Expressions */
static void
free_expression(struct Expression *expr)
{
  for (size_t i = 0; i < ARR_LENGTH(expr->parameters); ++i)
  {
    struct Parameter *param = ARR_GET(expr->parameters, i);
    free_parameter(param);
  }
  ARR_FREE(expr->parameters);
  for (size_t i = 0; i < ARR_LENGTH(expr->bindings); ++i)
  {
    Value *binding = *ARR_GET(expr->bindings, i);
    free_value(binding);
  }
  ARR_FREE(expr->bindings);
}

static char *
string_from_expression(const struct Expression *expr)
{
  size_t len = 5; /* two pairs of parentheses "()" and terminator. */
  char *path = string_from_symbol_path(expr->path);
  char *type = string_from_symbol_path(expr->type->path);
  len += strlen(path) + strlen(type) + 3; /* '[NAME] : [TYPE]' */

  if (ARR_LENGTH(expr->parameters) == 0)
  {
    char *str = malloc(len);
    char *c = str;
    *c = '(';
    ++c;
    strcpy(c, path);
    c += strlen(path);
    strcpy(c, " : ");
    c += 3;
    strcpy(c, type);
    c += strlen(type);
    *c = ')';
    ++c;
    strcpy(c, "()");
    c += 2;
    *c = '\0';
    free(path);
    free(type);
    return str;
  }
  else
  {
    bool first_param = TRUE;
    ARR(char *) param_types;
    ARR_INIT(param_types);
    for (size_t i = 0; i < ARR_LENGTH(expr->parameters); ++i)
    {
      if (!first_param)
        len += 2;
      if (first_param)
        first_param = FALSE;
      const struct Parameter *param = ARR_GET(expr->parameters, i);
      char *param_type = string_from_symbol_path(param->type->path);
      len += strlen(param->name) + strlen(param_type) + 3; /* '[NAME] : [TYPE]' */
      ARR_APPEND(param_types, param_type);
    }

    char *str = malloc(len);
    char *c = str;
    *c = '(';
    ++c;
    strcpy(c, path);
    c += strlen(path);
    strcpy(c, " : ");
    c += 3;
    strcpy(c, type);
    c += strlen(type);
    *c = ')';
    ++c;
    *c = '(';
    ++c;
    first_param = TRUE;
    for (size_t i = 0; i < ARR_LENGTH(expr->parameters); ++i)
    {
      if (!first_param)
      {
        strcpy(c, ", ");
        c += 2;
      }
      if (first_param)
        first_param = FALSE;
      const struct Parameter *param = ARR_GET(expr->parameters, i);
      char *param_type = *ARRAY_GET(param_types, char *, i);
      strcpy(c, param->name);
      c += strlen(param->name);
      strcpy(c, " : ");
      c += 3;
      strcpy(c, param_type);
      c += strlen(param_type);
      free(param_type);
    }
    *c = ')';
    ++c;
    *c = '\0';
    free(path);
    free(type);
    ARR_FREE(param_types);
    return str;
  }
}

/* Theorems. */
static void
free_theorem(struct Theorem *thm)
{
  for (size_t i = 0; i < ARR_LENGTH(thm->parameters); ++i)
  {
    struct Parameter *param = ARR_GET(thm->parameters, i);
    free_parameter(param);
  }
  ARR_FREE(thm->parameters);

  for (size_t i = 0; i < ARR_LENGTH(thm->assumptions); ++i)
  {
    struct Value *value = *ARR_GET(thm->assumptions, i);
    free_value(value);
  }
  ARR_FREE(thm->assumptions);

  for (size_t i = 0; i < ARR_LENGTH(thm->inferences); ++i)
  {
    struct Value *value = *ARR_GET(thm->inferences, i);
    free_value(value);
  }
  ARR_FREE(thm->inferences);
}

/* Symbols */
static void
free_symbol(struct Symbol *sym)
{
  free_symbol_path(sym->path);
  switch (sym->type)
  {
    case SymbolTypeType:
      free_type((struct Type *)sym->object);
      break;
    case SymbolTypeExpression:
      free_expression((struct Expression *)sym->object);
      break;
    case SymbolTypeTheorem:
      free_theorem((struct Theorem *)sym->object);
      break;
  }
  free(sym->object);
}

/* Core Logic */
LogicState *
new_logic_state(FILE *log_out)
{
  LogicState *state = malloc(sizeof(LogicState));
  ARR_INIT(state->symbol_table);
  state->next_id = 0;
  state->log_out = log_out;
  return state;
}

void
free_logic_state(LogicState *state)
{
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    struct Symbol *sym = ARR_GET(state->symbol_table, i);
    free_symbol(sym);
  }
  ARR_FREE(state->symbol_table);
  free(state);
}

bool
logic_state_path_occupied(const LogicState *state, const SymbolPath *path)
{
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    struct Symbol *sym = ARR_GET(state->symbol_table, i);
    if (symbol_paths_equal(sym->path, path))
      return TRUE;
  }
  return FALSE;
}

SymbolPath *
find_first_occupied_path(const LogicState *state, SymbolPath **paths)
{
  for (SymbolPath **path = paths; *path != NULL; ++path)
  {
    if (logic_state_path_occupied(state, *path))
      return copy_symbol_path(*path);
  }
  return NULL;
}

static struct Symbol *
locate_symbol(LogicState *state, const SymbolPath *path)
{
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    struct Symbol *sym = ARR_GET(state->symbol_table, i);
    if (symbol_paths_equal(sym->path, path))
      return sym;
  }
  return NULL;
}

static struct Symbol *
locate_symbol_with_type(LogicState *state, const SymbolPath *path,
  enum SymbolType type)
{
  struct Symbol *sym = locate_symbol(state, path);
  if (sym == NULL)
    return NULL;
  if (sym->type != type)
    return NULL;
  return sym;
}

static void
add_symbol(LogicState *state, struct Symbol sym)
{
  ARR_APPEND(state->symbol_table, sym);
}

LogicError
add_type(LogicState *state, struct PrototypeType proto)
{
  if (locate_symbol(state, proto.type_path) != NULL)
  {
    char *type_str = string_from_symbol_path(proto.type_path);
    LOG_NORMAL(state->log_out,
      "Cannot add type '%s' because the path is in use.\n", type_str);
    free(type_str);
    return LogicErrorSymbolAlreadyExists;
  }

  struct Type *t = malloc(sizeof(struct Type));
  t->id = state->next_id;
  ++state->next_id;
  t->atomic = proto.atomic;

  struct Symbol sym;
  sym.path = copy_symbol_path(proto.type_path);
  sym.type = SymbolTypeType;
  sym.object = t;

  t->path = sym.path;

  add_symbol(state, sym);

  char *type_str = string_from_symbol_path(proto.type_path);
  LOG_NORMAL(state->log_out, "Successfully added type '%s'.\n", type_str);
  free(type_str);

  return LogicErrorNone;
}

bool
types_equal(const struct Type *a, const struct Type *b)
{
  return (a->id == b->id) ? TRUE : FALSE;
}

LogicError
add_constant(LogicState *state, struct PrototypeConstant proto)
{
  if (locate_symbol(state, proto.constant_path) != NULL)
  {
    char *const_str = string_from_symbol_path(proto.constant_path);
    LOG_NORMAL(state->log_out,
      "Cannot add type '%s' because the path is in use.\n", const_str);
    free(const_str);
    return LogicErrorSymbolAlreadyExists;
  }

  struct Symbol *type_symbol = locate_symbol_with_type(state,
    proto.type_path, SymbolTypeType);
  if (type_symbol == NULL)
  {
    char *const_str = string_from_symbol_path(proto.constant_path);
    char *type_str = string_from_symbol_path(proto.type_path);
    LOG_NORMAL(state->log_out,
      "Cannot add expression '%s' because there is no such type '%s'.\n",
      const_str, type_str);
    free(const_str);
    free(type_str);
    return LogicErrorSymbolAlreadyExists;
  }

  struct Constant *c = malloc(sizeof(struct Constant));
  c->id = state->next_id;
  ++state->next_id;
  c->type = (struct Type *)type_symbol->object;
  if (proto.latex.segments != NULL)
  {
    c->has_latex = TRUE;
    ARR_INIT(c->latex.segments);
    for (struct PrototypeLatexFormatSegment **seg = proto.latex.segments;
      *seg != NULL; ++seg)
    {
      struct LatexFormatSegment new_seg;
      new_seg.is_variable = (*seg)->is_variable;
      new_seg.string = strdup((*seg)->string);
      ARR_APPEND(c->latex.segments, new_seg);
    }
  }
  else
  {
    c->has_latex = FALSE;
  }

  struct Symbol sym;
  sym.path = copy_symbol_path(proto.constant_path);
  sym.type = SymbolTypeConstant;
  sym.object = c;

  c->path = sym.path;

  add_symbol(state, sym);

  char *const_str = string_from_symbol_path(sym.path);
  LOG_NORMAL(state->log_out, "Successfully added constant '%s'.\n", const_str);
  free(const_str);

  return LogicErrorNone;
}

LogicError
add_expression(LogicState *state, struct PrototypeExpression proto)
{
  if (locate_symbol(state, proto.expression_path) != NULL)
  {
    char *expr_str = string_from_symbol_path(proto.expression_path);
    LOG_NORMAL(state->log_out,
      "Cannot add expression '%s' because the path is in use.\n", expr_str);
    free(expr_str);
    return LogicErrorSymbolAlreadyExists;
  }

  struct Expression *e = malloc(sizeof(struct Expression));
  e->id = state->next_id;
  ++state->next_id;

  struct Symbol *type_symbol = locate_symbol_with_type(state,
    proto.expression_type, SymbolTypeType);
  if (type_symbol == NULL)
  {
    char *expr_str = string_from_symbol_path(proto.expression_path);
    char *type_str = string_from_symbol_path(proto.expression_type);
    LOG_NORMAL(state->log_out,
      "Cannot add expression '%s' because there is no such type '%s'.\n",
      expr_str, type_str);
    free(expr_str);
    free(type_str);
    free(e);
    return LogicErrorSymbolAlreadyExists;
  }
  e->type = (struct Type *)type_symbol->object;
  if (proto.latex.segments != NULL)
  {
    e->has_latex = TRUE;
    ARR_INIT(e->latex.segments);
    for (struct PrototypeLatexFormatSegment **seg = proto.latex.segments;
      *seg != NULL; ++seg)
    {
      struct LatexFormatSegment new_seg;
      new_seg.is_variable = (*seg)->is_variable;
      new_seg.string = strdup((*seg)->string);
      ARR_APPEND(e->latex.segments, new_seg);
    }
  }
  else
  {
    e->has_latex = FALSE;
  }

  /* The type of the expression must not be atomic. */
  if (e->type->atomic)
  {
    char *expr_str = string_from_symbol_path(proto.expression_path);
    char *type_str = string_from_symbol_path(proto.expression_type);
    LOG_NORMAL(state->log_out,
      "Cannot add expression '%s' because the type '%s' is atomic.\n",
      expr_str, type_str);
    free(expr_str);
    free(type_str);
    free(e);
    return LogicErrorSymbolAlreadyExists;
  }

  ARR_INIT(e->parameters);
  for (struct PrototypeParameter **param = proto.parameters;
    *param != NULL; ++param)
  {
    struct Parameter p;
    type_symbol = locate_symbol_with_type(state,
      (*param)->type, SymbolTypeType);
    if (type_symbol == NULL)
    {
      char *expr_str = string_from_symbol_path(proto.expression_path);
      char *type_str = string_from_symbol_path((*param)->type);
      LOG_NORMAL(state->log_out,
        "Cannot add expression '%s' because there is no such type '%s'.\n",
        expr_str, type_str);
      free(expr_str);
      free(type_str);
      free_expression(e);
      free(e);
      return LogicErrorSymbolAlreadyExists;
    }
    p.type = (struct Type *)type_symbol->object;
    p.name = strdup((*param)->name);
    ARR_APPEND(e->parameters, p);
  }

  ARR_INIT(e->bindings);
  if (proto.bindings != NULL)
  {
    for (Value **binding = proto.bindings; *binding != NULL; ++binding)
    {
      ARR_APPEND(e->bindings, copy_value(*binding));
    }
  }

  struct Symbol sym;
  sym.path = copy_symbol_path(proto.expression_path);
  sym.type = SymbolTypeExpression;
  sym.object = e;

  e->path = sym.path;

  add_symbol(state, sym);

  char *expr_str = string_from_symbol_path(proto.expression_path);
  LOG_NORMAL(state->log_out,
    "Successfully added expression '%s'.\n", expr_str);
  free(expr_str);
  if (verbose)
  {
    expr_str = string_from_expression(e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);

    for (size_t i = 0; i < ARR_LENGTH(e->bindings); ++i)
    {
      Value *binding = *ARR_GET(e->bindings, i);
      char *binding_str = string_from_value(binding);
      LOG_VERBOSE(state->log_out, "Binds: '%s'.\n", binding_str);
      free(binding_str);
    }
  }

  return LogicErrorNone;
}

/* Values */
Value *
new_variable_value(LogicState *state, const char *name, const SymbolPath *type)
{
  Value *value = malloc(sizeof(Value));

  value->variable_name = strdup(name);
  value->value_type = ValueTypeVariable;
  value->bound = FALSE;
  struct Symbol *type_symbol = locate_symbol_with_type(state,
    type, SymbolTypeType);
  if (type_symbol == NULL)
  {
    char *type_str = string_from_symbol_path(type);
    LOG_NORMAL(state->log_out,
      "Cannot create value because there is no such type '%s'.\n", type_str);
    free(type_str);
    free(value->variable_name);
    free(value);
    return NULL;
  }
  value->type = (struct Type *)type_symbol->object;

  return value;
}

Value *
new_constant_value(LogicState *state, const SymbolPath *constant)
{
  Value *value = malloc(sizeof(Value));

  value->value_type = ValueTypeConstant;
  value->bound = FALSE;
  struct Symbol *constant_symbol = locate_symbol_with_type(state,
    constant, SymbolTypeConstant);
  if (constant_symbol == NULL)
  {
    char *const_str = string_from_symbol_path(constant);
    LOG_NORMAL(state->log_out,
      "Cannot create value because there is no such constant '%s'.\n", const_str);
    free(const_str);
    free(value);
    return NULL;
  }
  value->constant = (struct Constant *)constant_symbol->object;
  value->type = value->constant->type;

  return value;
}

Value *
new_composition_value(LogicState *state, const SymbolPath *expr_path,
  Value * const *args)
{
  Value *value = malloc(sizeof(Value));

  value->value_type = ValueTypeComposition;
  value->bound = FALSE;
  struct Symbol *expr_symbol = locate_symbol_with_type(state,
    expr_path, SymbolTypeExpression);
  if (expr_symbol == NULL)
  {
    char *expr_str = string_from_symbol_path(expr_path);
    LOG_NORMAL(state->log_out,
      "Cannot create value because there is no such expression '%s'.\n",
      expr_str);
    free(expr_str);
    free(value);
    return NULL;
  }
  value->expression = (struct Expression *)expr_symbol->object;
  value->type = value->expression->type;

  ARR_INIT(value->arguments);
  for (Value * const *arg = args;
    *arg != NULL; ++arg)
  {
    ARR_APPEND(value->arguments, copy_value(*arg));
  }

  /* Make sure that the arguments match the types of the parameters of
     the expression. */
  if (ARR_LENGTH(value->arguments) != ARR_LENGTH(value->expression->parameters))
  {
    char *expr_str = string_from_symbol_path(expr_path);
    LOG_NORMAL(state->log_out,
      "Cannot create value because the wrong number of arguments are supplied to the expression '%s'\n",
      expr_str);
    free(expr_str);
    free_value(value);
    return NULL;
  }
  ArgumentArray args_array;
  ARR_INIT(args_array);
  for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
  {
    Value *arg = *ARR_GET(value->arguments, i);
    const struct Parameter *param = ARR_GET(value->expression->parameters, i);
    struct Argument argument;
    argument.name = strdup(param->name);
    argument.value = copy_value(arg);
    ARR_APPEND(args_array, argument);
    if (!types_equal(arg->type, param->type))
    {
      char *expr_str = string_from_symbol_path(expr_path);
      LOG_NORMAL(state->log_out,
        "Cannot create value because the type of an argument does not match the required value of the corresponding parameter of expression '%s'\n",
        expr_str);
      free(expr_str);
      free_value(value);
      return NULL;
    }
  }

  /* Look for things to bind. */
  /* TODO: things are getting bound that should be free, like constants. */
  for (size_t i = 0; i < ARR_LENGTH(value->expression->bindings); ++i)
  {
    const Value *binding = *ARR_GET(value->expression->bindings, i);
    Value *instantiated = instantiate_value(state, binding, args_array);

    ValueArray occurrences;
    ARR_INIT(occurrences);
    enumerate_value_occurrences(instantiated, value, &occurrences);
    for (size_t j = 0; j < ARR_LENGTH(occurrences); ++j)
    {
      Value *occurrence = *ARR_GET(occurrences, j);
      occurrence->bound = TRUE;
    }
    ARR_FREE(occurrences);

    free_value(instantiated);
  }

  return value;
}

LogicError
add_axiom(LogicState *state, struct PrototypeTheorem proto)
{
  if (locate_symbol(state, proto.theorem_path) != NULL)
  {
    char *axiom_str = string_from_symbol_path(proto.theorem_path);
    LOG_NORMAL(state->log_out,
      "Cannot add axiom '%s' because the path is in use.\n", axiom_str);
    free(axiom_str);
    return LogicErrorSymbolAlreadyExists;
  }

  struct Theorem *a = malloc(sizeof(struct Theorem));
  a->is_axiom = TRUE;
  a->id = state->next_id;
  ++state->next_id;

  /* Parameters. */
  ARR_INIT(a->parameters);
  for (struct PrototypeParameter **param = proto.parameters;
    *param != NULL; ++param)
  {
    struct Parameter p;
    const struct Symbol *type_symbol = locate_symbol_with_type(state,
      (*param)->type, SymbolTypeType);
    if (type_symbol == NULL)
    {
      char *axiom_str = string_from_symbol_path(proto.theorem_path);
      char *type_str = string_from_symbol_path((*param)->type);
      LOG_NORMAL(state->log_out,
        "Cannot add axiom '%s' because there is no such type '%s'.\n",
        axiom_str, type_str);
      free(axiom_str);
      free(type_str);
      //free_expression(e);
      free(a);
      return LogicErrorSymbolAlreadyExists;
    }
    p.type = (struct Type *)type_symbol->object;
    p.name = strdup((*param)->name);
    ARR_APPEND(a->parameters, p);
  }

  /* Requirements. */
  ARR_INIT(a->requirements);
  for (struct PrototypeRequirement **req = proto.requirements;
    *req != NULL; ++req)
  {
    struct Requirement requirement;

    ARR_INIT(requirement.arguments);
    for (Value **arg = (*req)->arguments; *arg != NULL; ++arg)
    {
      ARR_APPEND(requirement.arguments, copy_value(*arg));
    }

    /* Make sure that the number of arguments match the type. */
    /* TODO: make validation of requirements its own function. */

    if (strcmp((*req)->require, "free_for") == 0)
    {
      requirement.type = RequirementTypeFreeFor;
      if (ARR_LENGTH(requirement.arguments) != 3)
        return LogicErrorSymbolAlreadyExists;
    }
    else if (strcmp((*req)->require, "not_free") == 0)
    {
      requirement.type = RequirementTypeNotFree;
      if (ARR_LENGTH(requirement.arguments) != 2)
        return LogicErrorSymbolAlreadyExists;
    }
    else if (strcmp((*req)->require, "substitution") == 0)
    {
      requirement.type = RequirementTypeSubstitution;
      if (ARR_LENGTH(requirement.arguments) != 4)
        return LogicErrorSymbolAlreadyExists;
    }
    else if (strcmp((*req)->require, "full_substitution") == 0)
    {
      requirement.type = RequirementTypeFullSubstitution;
      if (ARR_LENGTH(requirement.arguments) != 4)
        return LogicErrorSymbolAlreadyExists;
    }
    else
    {
      /* TODO: just ignore this requirement? */
      continue;
    }

    ARR_APPEND(a->requirements, requirement);
  }

  /* Assumptions & inferences. */
  ARR_INIT(a->assumptions);
  ARR_INIT(a->inferences);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARR_APPEND(a->assumptions, copy_value(*assume));
  }
  for (Value **infer = proto.inferences;
    *infer != NULL; ++infer)
  {
    ARR_APPEND(a->inferences, copy_value(*infer));
  }

  struct Symbol sym;
  sym.path = copy_symbol_path(proto.theorem_path);
  sym.type = SymbolTypeTheorem;
  sym.object = a;

  a->path = sym.path;

  add_symbol(state, sym);

  char *axiom_str = string_from_symbol_path(proto.theorem_path);
  LOG_NORMAL(state->log_out,
    "Successfully added axiom '%s'.\n", axiom_str);
  free(axiom_str);

  if (verbose)
  {
    for (size_t i = 0; i < ARR_LENGTH(a->assumptions); ++i)
    {
      char *str = string_from_value(*ARR_GET(a->assumptions, i));
      printf("Assumption %zu: %s\n", i, str);
      free(str);
    }
    for (size_t i = 0; i < ARR_LENGTH(a->inferences); ++i)
    {
      char *str = string_from_value(*ARR_GET(a->inferences, i));
      printf("Inference %zu: %s\n", i, str);
      free(str);
    }
    /*expr_str = string_from_expression(e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);*/
  }

  return LogicErrorNone;
}

static bool
statement_proven(const Value *statement, ValueArray proven)
{
  for (size_t i = 0; i < ARR_LENGTH(proven); ++i)
  {
    const Value *s = *ARR_GET(proven, i);
    if (values_equal(statement, s))
      return TRUE;
  }
  return FALSE;
}

int
instantiate_theorem(struct LogicState *state,
  const struct Theorem *src, ArgumentArray args, ValueArray *proven, bool force)
{
  /* Check the requirements. */
  if (!force)
  {
    for (size_t i = 0; i < ARR_LENGTH(src->requirements); ++i)
    {
      bool satisfied = FALSE;
      const struct Requirement *req = ARR_GET(src->requirements, i);

      ARR(Value *) instantiated_args;
      ARR_INIT(instantiated_args);
      for (size_t j = 0; j < ARR_LENGTH(req->arguments); ++j)
      {
        const Value *arg = *ARR_GET(req->arguments, j);
        Value *instantiated = instantiate_value(state, arg, args);
        ARR_APPEND(instantiated_args, instantiated);
      }

      switch (req->type)
      {
        case RequirementTypeFreeFor:
          {
            if (ARR_LENGTH(instantiated_args) != 3)
            {
              LOG_NORMAL(state->log_out,
                "Requirement has wrong number of arguments");
              return 1;
            }
            const Value *source = *ARR_GET(instantiated_args, 0);
            const Value *target = *ARR_GET(instantiated_args, 1);
            const Value *context = *ARR_GET(instantiated_args, 2);
            satisfied = evaluate_free_for(state, source, target, context);
          }
          break;
        case RequirementTypeNotFree:
          {
            if (ARR_LENGTH(instantiated_args) != 2)
            {
              LOG_NORMAL(state->log_out,
                "Requirement has wrong number of arguments");
              return 1;
            }
            const Value *target = *ARR_GET(instantiated_args, 0);
            const Value *context = *ARR_GET(instantiated_args, 1);
            satisfied = evaluate_not_free(state, target, context);
          }
          break;
        case RequirementTypeSubstitution:
          {
            if (ARR_LENGTH(instantiated_args) != 4)
            {
              LOG_NORMAL(state->log_out,
                "Requirement has wrong number of arguments");
              return 1;
            }
            const Value *target = *ARR_GET(instantiated_args, 0);
            const Value *context = *ARR_GET(instantiated_args, 1);
            const Value *source = *ARR_GET(instantiated_args, 2);
            const Value *new_context = *ARR_GET(instantiated_args, 3);
            satisfied = evaluate_substitution(state, target, context,
              source, new_context);
          }
          break;
        case RequirementTypeFullSubstitution:
          {
            if (ARR_LENGTH(instantiated_args) != 4)
            {
              LOG_NORMAL(state->log_out,
                "Requirement has wrong number of arguments");
              return 1;
            }
            const Value *target = *ARR_GET(instantiated_args, 0);
            const Value *context = *ARR_GET(instantiated_args, 1);
            const Value *source = *ARR_GET(instantiated_args, 2);
            const Value *new_context = *ARR_GET(instantiated_args, 3);
            satisfied = evaluate_full_substitution(state, target, context,
              source, new_context);
          }
          break;
      }

      if (!satisfied)
        return 1;
    }

    /* First, instantiate the assumptions. */
    ARR(Value *) instantiated_assumptions;
    ARR_INIT(instantiated_assumptions);
    for (size_t i = 0; i < ARR_LENGTH(src->assumptions); ++i)
    {
      const Value *assumption = *ARR_GET(src->assumptions, i);
      Value *instantiated = instantiate_value(state, assumption, args);
      if (instantiated == NULL)
        return 1;
      ARR_APPEND(instantiated_assumptions, instantiated);
    }

    /* Verify that each assumption has been proven. */
    for (size_t i = 0; i < ARR_LENGTH(instantiated_assumptions); ++i)
    {
      Value *assumption = *ARR_GET(instantiated_assumptions, i);
      if (!statement_proven(assumption, *proven))
      {
        char *theorem_str = string_from_symbol_path(src->path);
        char *assumption_str = string_from_value(assumption);
        LOG_NORMAL(state->log_out,
          "Cannot instantiate theorem '%s' because the assumption '%s' is not satisfied.\n",
          theorem_str, assumption_str);
        free(theorem_str);
        free(assumption_str);
        return 1;
      }
      free_value(assumption);
    }
    ARR_FREE(instantiated_assumptions);
  }

  /* Add all the inferences to the environment as proven statements. */
  for (size_t i = 0; i < ARR_LENGTH(src->inferences); ++i)
  {
    const Value *inference = *ARR_GET(src->inferences, i);
    Value *instantiated = instantiate_value(state, inference, args);
    if (instantiated == NULL)
      return 1;
    ARR_APPEND(*proven, instantiated);
  }

  return 0;
}

static void
list_proven(LogicState *state, ValueArray proven)
{
  LOG_NORMAL(state->log_out, "Statements proven:\n");
  for (size_t i = 0; i < ARR_LENGTH(proven); ++i)
  {
    Value *stmt = *ARR_GET(proven, i);
    char *str = string_from_value(stmt);
    LOG_NORMAL(state->log_out, "> '%s'\n", str);
    free(str);
  }
}

/* TODO: The return value should be a struct, or modify the PrototypeTheorem,
   in order to propagate errors with full detail. */
LogicError
add_theorem(LogicState *state, struct PrototypeTheorem proto)
{
  if (locate_symbol(state, proto.theorem_path) != NULL)
  {
    char *axiom_str = string_from_symbol_path(proto.theorem_path);
    LOG_NORMAL(state->log_out,
      "Cannot add theorem '%s' because the path is in use.\n", axiom_str);
    free(axiom_str);
    return LogicErrorSymbolAlreadyExists;
  }

  struct Theorem *a = malloc(sizeof(struct Theorem));
  a->is_axiom = FALSE;
  a->id = state->next_id;
  ++state->next_id;

  /* Parameters. */
  ARR_INIT(a->parameters);
  for (struct PrototypeParameter **param = proto.parameters;
    *param != NULL; ++param)
  {
    struct Parameter p;
    const struct Symbol *type_symbol = locate_symbol_with_type(state,
      (*param)->type, SymbolTypeType);
    if (type_symbol == NULL)
    {
      char *axiom_str = string_from_symbol_path(proto.theorem_path);
      char *type_str = string_from_symbol_path((*param)->type);
      LOG_NORMAL(state->log_out,
        "Cannot add theorem '%s' because there is no such type '%s'.\n",
        axiom_str, type_str);
      free(axiom_str);
      free(type_str);
      //free_expression(e);
      free(a);
      return LogicErrorSymbolAlreadyExists;
    }
    p.type = (struct Type *)type_symbol->object;
    p.name = strdup((*param)->name);
    ARR_APPEND(a->parameters, p);
  }

  ARR_INIT(a->requirements);

  /* Assumptions & inferences. */
  ARR_INIT(a->assumptions);
  ARR_INIT(a->inferences);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARR_APPEND(a->assumptions, copy_value(*assume));
  }
  for (Value **infer = proto.inferences;
    *infer != NULL; ++infer)
  {
    ARR_APPEND(a->inferences, copy_value(*infer));
  }

  /* Finally, check the proof. */
  ValueArray proven;
  ARR_INIT(proven);
  ARR_INIT(a->steps);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARR_APPEND(proven, copy_value(*assume));
  }
  for (struct PrototypeProofStep **step = proto.steps;
    *step != NULL; ++step)
  {
    struct TheoremReference ref;
    ARR_INIT(ref.arguments);
    const struct Symbol *thm_symbol = locate_symbol_with_type(state,
      (*step)->theorem_path, SymbolTypeTheorem);
    if (thm_symbol == NULL)
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced in proof does not exist.\n");
      return LogicErrorSymbolAlreadyExists;
    }
    ref.theorem = (struct Theorem *)thm_symbol->object;

    /* Build a list of arguments. */
    size_t args_n = 0;
    for (Value **arg = (*step)->arguments; *arg != NULL; ++arg)
      ++args_n;
    if (args_n != ARR_LENGTH(ref.theorem->parameters))
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced received the wrong number of arguments.\n");
      return LogicErrorSymbolAlreadyExists;
    }

    ArgumentArray args;
    ARR_INIT(args);
    for (size_t i = 0; i < args_n; ++i)
    {
      struct Parameter *param = ARR_GET(ref.theorem->parameters, i);

      struct Argument arg;
      arg.name = strdup(param->name);
      arg.value = copy_value((*step)->arguments[i]);

      ARR_APPEND(ref.arguments, copy_value(arg.value));

      if (!types_equal(param->type, arg.value->type))
      {
        LOG_NORMAL(state->log_out,
          "Cannot add theorem because an axiom/theorem referenced received an argument with the wrong type.\n");
        return LogicErrorSymbolAlreadyExists;
      }

      ARR_APPEND(args, arg);
    }

    if (instantiate_theorem(state, ref.theorem, args, &proven, FALSE) != 0)
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced could not be instantiated.\n");
      list_proven(state, proven);
      return LogicErrorSymbolAlreadyExists;
    }

    for (size_t i = 0; i < args_n; ++i)
    {
      struct Argument *arg = ARR_GET(args, i);
      free(arg->name);
      free_value(arg->value);
    }
    ARR_FREE(args);
    ARR_APPEND(a->steps, ref);
  }

  /* Check that all the inferences have been proven. */
  for (size_t i = 0; i < ARR_LENGTH(a->inferences); ++i)
  {
    Value *infer = *ARR_GET(a->inferences, i);
    if (!statement_proven(infer, proven))
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an inference was not proven.\n");
      return LogicErrorSymbolAlreadyExists;
    }
  }

  /* Free all the statements that we've proven. */
  for (size_t i = 0; i < ARR_LENGTH(proven); ++i)
  {
    Value *v = *ARR_GET(proven, i);
    free_value(v);
  }
  ARR_FREE(proven);

  struct Symbol sym;
  sym.path = copy_symbol_path(proto.theorem_path);
  sym.type = SymbolTypeTheorem;
  sym.object = a;

  a->path = sym.path;

  add_symbol(state, sym);

  char *axiom_str = string_from_symbol_path(proto.theorem_path);
  LOG_NORMAL(state->log_out,
    "Successfully added theorem '%s'.\n", axiom_str);
  free(axiom_str);

  if (verbose)
  {
    for (size_t i = 0; i < ARR_LENGTH(a->assumptions); ++i)
    {
      char *str = string_from_value(*ARR_GET(a->assumptions, i));
      printf("Assumption %zu: %s\n", i, str);
      free(str);
    }
    for (size_t i = 0; i < ARR_LENGTH(a->inferences); ++i)
    {
      char *str = string_from_value(*ARR_GET(a->inferences, i));
      printf("Inference %zu: %s\n", i, str);
      free(str);
    }
    /*expr_str = string_from_expression(e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);*/
  }

  return LogicErrorNone;
}
