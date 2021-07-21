#include "logic.h"
#include "sl.h"
#include <string.h>

#include "core.h"

/* Paths */
SymbolPath *
init_symbol_path()
{
  SymbolPath *path = malloc(sizeof(SymbolPath));
  ARRAY_INIT(path->segments, char *);
  return path;
}

SymbolPath *
copy_symbol_path(const SymbolPath *src)
{
  SymbolPath *dst = init_symbol_path();
  for (size_t i = 0; i < ARRAY_LENGTH(src->segments); ++i)
  {
    ARRAY_APPEND(dst->segments, char *,
      strdup(*ARRAY_GET(src->segments, char *, i)));
  }
  return dst;
}

void
free_symbol_path(SymbolPath *path)
{
  for (size_t i = 0; i < ARRAY_LENGTH(path->segments); ++i)
  {
    free(*ARRAY_GET(path->segments, char *, i));
  }
  ARRAY_FREE(path->segments);
  free(path);
}

int
length_of_symbol_path(const SymbolPath *path)
{
  return ARRAY_LENGTH(path->segments);
}

const char *
get_symbol_path_segment(const SymbolPath *path, size_t index)
{
  return *ARRAY_GET(path->segments, char *, index);
}

const char *
get_symbol_path_last_segment(const SymbolPath *path)
{
  return get_symbol_path_segment(path, length_of_symbol_path(path) - 1);
}

char *
string_from_symbol_path(const SymbolPath *path)
{
  if (ARRAY_LENGTH(path->segments) == 0)
    return strdup("");
  size_t str_len = ARRAY_LENGTH(path->segments);
  for (size_t i = 0; i < ARRAY_LENGTH(path->segments); ++i)
  {
    const char *segment = *ARRAY_GET(path->segments, char *, i);
    str_len += strlen(segment);
  }
  char *str = malloc(str_len);
  char *c = str;
  for (size_t i = 0; i < ARRAY_LENGTH(path->segments); ++i)
  {
    if (i > 0)
    {
      *c = '.';
      ++c;
    }
    const char *segment = *ARRAY_GET(path->segments, char *, i);
    strcpy(c, segment);
    c += strlen(segment);
  }
  *c = '\0';
  return str;
}

void
push_symbol_path(SymbolPath *path, const char *segment)
{
  ARRAY_APPEND(path->segments, char *, strdup(segment));
}

void
pop_symbol_path(SymbolPath *path)
{
  free(*ARRAY_GET(path->segments, char *, ARRAY_LENGTH(path->segments) - 1));
  ARRAY_POP(path->segments);
}

void
append_symbol_path(SymbolPath *path, const SymbolPath *to_append)
{
  for (size_t i = 0; i < ARRAY_LENGTH(to_append->segments); ++i)
  {
    const char *segment = *ARRAY_GET(to_append->segments, char *, i);
    push_symbol_path(path, segment);
  }
}

bool
symbol_paths_equal(const SymbolPath *a, const SymbolPath *b)
{
  if (ARRAY_LENGTH(a->segments) != ARRAY_LENGTH(b->segments))
    return FALSE;
  for (size_t i = 0; i < ARRAY_LENGTH(a->segments); ++i)
  {
    const char *a_segment = *ARRAY_GET(a->segments, char *, i);
    const char *b_segment = *ARRAY_GET(b->segments, char *, i);
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
  for (size_t i = 0; i < ARRAY_LENGTH(expr->parameters); ++i)
  {
    struct Parameter *param =
      ARRAY_GET(expr->parameters, struct Parameter, i);
    free_parameter(param);
  }
  ARRAY_FREE(expr->parameters);
  for (size_t i = 0; i < ARRAY_LENGTH(expr->bindings); ++i)
  {
    Value *binding = *ARRAY_GET(expr->bindings, Value *, i);
    free_value(binding);
  }
  ARRAY_FREE(expr->bindings);
}

static char *
string_from_expression(const struct Expression *expr)
{
  size_t len = 5; /* two pairs of parentheses "()" and terminator. */
  char *path = string_from_symbol_path(expr->path);
  char *type = string_from_symbol_path(expr->type->path);
  len += strlen(path) + strlen(type) + 3; /* '[NAME] : [TYPE]' */

  if (ARRAY_LENGTH(expr->parameters) == 0)
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
    Array param_types;
    ARRAY_INIT(param_types, char *);
    for (size_t i = 0; i < ARRAY_LENGTH(expr->parameters); ++i)
    {
      if (!first_param)
        len += 2;
      if (first_param)
        first_param = FALSE;
      const struct Parameter *param =
        ARRAY_GET(expr->parameters, struct Parameter, i);
      char *param_type = string_from_symbol_path(param->type->path);
      len += strlen(param->name) + strlen(param_type) + 3; /* '[NAME] : [TYPE]' */
      ARRAY_APPEND(param_types, char *, param_type);
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
    for (size_t i = 0; i < ARRAY_LENGTH(expr->parameters); ++i)
    {
      if (!first_param)
      {
        strcpy(c, ", ");
        c += 2;
      }
      if (first_param)
        first_param = FALSE;
      const struct Parameter *param =
        ARRAY_GET(expr->parameters, struct Parameter, i);
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
    ARRAY_FREE(param_types);
    return str;
  }
}

/* Theorems. */
static void
free_theorem(struct Theorem *thm)
{
  for (size_t i = 0; i < ARRAY_LENGTH(thm->parameters); ++i)
  {
    struct Parameter *param =
      ARRAY_GET(thm->parameters, struct Parameter, i);
    free_parameter(param);
  }
  ARRAY_FREE(thm->parameters);

  for (size_t i = 0; i < ARRAY_LENGTH(thm->assumptions); ++i)
  {
    struct Value *value =
      *ARRAY_GET(thm->assumptions, struct Value *, i);
    free_value(value);
  }
  ARRAY_FREE(thm->assumptions);

  for (size_t i = 0; i < ARRAY_LENGTH(thm->inferences); ++i)
  {
    struct Value *value =
      *ARRAY_GET(thm->inferences, struct Value *, i);
    free_value(value);
  }
  ARRAY_FREE(thm->inferences);
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
  ARRAY_INIT(state->symbol_table, struct Symbol);
  state->next_id = 0;
  state->log_out = log_out;
  return state;
}

void
free_logic_state(LogicState *state)
{
  for (size_t i = 0; i < ARRAY_LENGTH(state->symbol_table); ++i)
  {
    struct Symbol *sym =
      ARRAY_GET(state->symbol_table, struct Symbol, i);
    free_symbol(sym);
  }
  ARRAY_FREE(state->symbol_table);
  free(state);
}

bool
logic_state_path_occupied(const LogicState *state, const SymbolPath *path)
{
  for (size_t i = 0; i < ARRAY_LENGTH(state->symbol_table); ++i)
  {
    struct Symbol *sym =
      ARRAY_GET(state->symbol_table, struct Symbol, i);
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
  for (size_t i = 0; i < ARRAY_LENGTH(state->symbol_table); ++i)
  {
    struct Symbol *sym =
      ARRAY_GET(state->symbol_table, struct Symbol, i);
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
  ARRAY_APPEND(state->symbol_table, struct Symbol, sym);
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

static bool
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
  if (proto.latex != NULL)
    c->latex = strdup(proto.latex);
  else
    c->latex = NULL;

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
  if (proto.latex != NULL)
    e->latex = strdup(proto.latex);
  else
    e->latex = NULL;

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

  ARRAY_INIT(e->parameters, struct Parameter);
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
    ARRAY_APPEND(e->parameters, struct Parameter, p);
  }

  ARRAY_INIT(e->bindings, Value *);
  if (proto.bindings != NULL)
  {
    for (Value **binding = proto.bindings; *binding != NULL; ++binding)
    {
      ARRAY_APPEND(e->bindings, Value *, copy_value(*binding));
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

    for (size_t i = 0; i < ARRAY_LENGTH(e->bindings); ++i)
    {
      Value *binding = *ARRAY_GET(e->bindings, Value *, i);
      char *binding_str = string_from_value(binding);
      LOG_VERBOSE(state->log_out, "Binds: '%s'.\n", binding_str);
      free(binding_str);
    }
  }

  return LogicErrorNone;
}

/* Values */
void
free_value(Value *value)
{
  if (value->value_type == ValueTypeVariable)
  {
    free(value->variable_name);
  }
  else if (value->value_type == ValueTypeConstant)
  {

  }
  else if (value->value_type == ValueTypeComposition)
  {
    for (size_t i = 0; i < ARRAY_LENGTH(value->arguments); ++i)
    {
      Value *arg = *ARRAY_GET(value->arguments, Value *, i);
      free_value(arg);
    }
    ARRAY_FREE(value->arguments);
  }
  free(value);
}

static void
copy_value_to(Value *dst, const Value *src)
{
  dst->value_type = src->value_type;
  dst->type = src->type;
  dst->bound = src->bound;
  if (src->value_type == ValueTypeVariable)
  {
    dst->variable_name = strdup(src->variable_name);
  }
  else if (src->value_type == ValueTypeConstant)
  {
    dst->constant = src->constant;
  }
  else if (src->value_type == ValueTypeComposition)
  {
    dst->expression = src->expression;
    ARRAY_INIT(dst->arguments, Value *);
    for (size_t i = 0; i < ARRAY_LENGTH(src->arguments); ++i)
    {
      const struct Value *arg =
        *ARRAY_GET(src->arguments, Value *, i);
      struct Value *arg_copy = copy_value(arg);
      ARRAY_APPEND(dst->arguments, Value *, arg_copy);
    }
  }
}

Value *
copy_value(const Value *value)
{
  Value *v = malloc(sizeof(Value));
  copy_value_to(v, value);
  return v;
}

bool
values_equal(const Value *a, const Value *b)
{
  /* DO NOT compare `bound`. */
  if (a->value_type != b->value_type)
    return FALSE;
  switch (a->value_type)
  {
    case ValueTypeConstant:
      if (a->constant != b->constant) /* TODO: test for equivalence of constants, not for pointer equality. */
        return FALSE;
      break;
    case ValueTypeVariable:
      if (!types_equal(a->type, b->type))
        return FALSE;
      if (strcmp(a->variable_name, b->variable_name) != 0)
        return FALSE;
      break;
    case ValueTypeComposition:
      if (!types_equal(a->type, b->type))
        return FALSE;
      if (a->expression != b->expression) /* TODO: Use an equivalence function instead of pointer equality. */
        return FALSE;
      if (ARRAY_LENGTH(a->arguments) != ARRAY_LENGTH(b->arguments))
        return FALSE;
      for (size_t i = 0; i < ARRAY_LENGTH(a->arguments); ++i)
      {
        const Value *arg_a = *ARRAY_GET(a->arguments, Value *, i);
        const Value *arg_b = *ARRAY_GET(b->arguments, Value *, i);
        if (!values_equal(arg_a, arg_b))
          return FALSE;
      }
      break;
  }
  return TRUE;
}

bool
value_terminal(const Value *v)
{
  switch (v->value_type)
  {
    case ValueTypeConstant:
      return TRUE;
      break;
    case ValueTypeVariable:
      return v->type->atomic;
      break;
    case ValueTypeComposition:
      for (size_t i = 0; i < ARRAY_LENGTH(v->arguments); ++i)
      {
        Value *arg = *ARRAY_GET(v->arguments, Value *, i);
        if (!value_terminal(arg))
          return FALSE;
      }
      return TRUE;
      break;
  }
}

char *
string_from_value(const Value *value)
{
  switch (value->value_type)
  {
    case ValueTypeComposition:
      {
        char *expr_str = string_from_symbol_path(value->expression->path);
        char *str;
        if (ARRAY_LENGTH(value->arguments) == 0)
        {
          size_t len = 3 + strlen(expr_str);
          if (value->bound)
            len += 1;
          str = malloc(len);
          char *c = str;
          if (value->bound)
          {
            *c = '!';
            ++c;
          }
          strcpy(c, expr_str);
          c += strlen(expr_str);
          strcpy(c, "()");
          c += 2;
          *c = '\0';
          return str;
        }
        else
        {
          size_t len = 3 + strlen(expr_str);
          if (value->bound)
            len += 1;
          char **args = malloc(sizeof(char *) * ARRAY_LENGTH(value->arguments));
          for (size_t i = 0; i < ARRAY_LENGTH(value->arguments); ++i)
          {
            const struct Value *arg =
              *ARRAY_GET(value->arguments, struct Value *, i);
            args[i] = string_from_value(arg);
            len += strlen(args[i]);
          }
          len += (ARRAY_LENGTH(value->arguments) - 1) * 2;

          str = malloc(len);
          char *c = str;
          if (value->bound)
          {
            *c = '!';
            ++c;
          }
          strcpy(c, expr_str);
          c += strlen(expr_str);
          *c = '(';
          ++c;
          bool first_arg = TRUE;
          for (size_t i = 0; i < ARRAY_LENGTH(value->arguments); ++i)
          {
            if (!first_arg)
            {
              strcpy(c, ", ");
              c += 2;
            }
            if (first_arg)
              first_arg = FALSE;
            strcpy(c, args[i]);
            c += strlen(args[i]);
            free(args[i]);
          }
          free(args);
          *c = ')';
          ++c;
          *c = '\0';
          ++c;
        }
        free(expr_str);
        return str;
      }
      break;
    case ValueTypeConstant:
      {
        char *const_str = string_from_symbol_path(value->constant->path);
        size_t len = 1 + strlen(const_str);
        if (value->bound)
          len += 1;
        char *str = malloc(len);
        char *c = str;
        if (value->bound)
        {
          *c = '!';
          ++c;
        }
        strcpy(c, const_str);
        c += strlen(const_str);
        *c = '\0';
        free(const_str);
        return str;
      }
      break;
    case ValueTypeVariable:
      {
        size_t len = 2 + strlen(value->variable_name);
        if (value->bound)
          len += 1;
        char *str = malloc(len);
        char *c = str;
        if (value->bound)
        {
          *c = '!';
          ++c;
        }
        *c = '$';
        ++c;
        strcpy(c, value->variable_name);
        c += strlen(value->variable_name);
        *c = '\0';
        return str;
      }
      break;
  }
}

static void
enumerate_value_occurrences(const Value *target, const Value *search_in,
  Array *occurrences)
{
  if (values_equal(target, search_in))
  {
    ARRAY_APPEND(*occurrences, const Value *, search_in);
  }
  else if (search_in->value_type == ValueTypeComposition)
  {
    for (size_t i = 0; i < ARRAY_LENGTH(search_in->arguments); ++i)
    {
      const Value *arg = *ARRAY_GET(search_in->arguments, Value *, i);
      enumerate_value_occurrences(target, arg, occurrences);
    }
  }
}

struct Argument
{
  char *name;
  Value *value;
};

static Value *
instantiate_value(struct LogicState *state, const Value *src, Array args)
{
  switch (src->value_type)
  {
    case ValueTypeConstant:
      return copy_value(src);
      break;
    case ValueTypeVariable:
      /* Find the corresponding argument. */
      {
        const struct Argument *arg = NULL;
        for (size_t i = 0; i < ARRAY_LENGTH(args); ++i)
        {
          const struct Argument *a = ARRAY_GET(args, struct Argument, i);
          if (strcmp(a->name, src->variable_name) == 0)
          {
            arg = a;
            break;
          }
        }
        if (arg == NULL)
        {
          char *value_str = string_from_value(src);
          LOG_NORMAL(state->log_out,
            "Cannot instantiate value '%s' because there is no matching argument.\n",
            value_str);
          free(value_str);
          return NULL;
        }
        if (!types_equal(arg->value->type, src->type))
        {
          char *value_str = string_from_value(src);
          char *src_type = string_from_symbol_path(src->type->path);
          char *arg_type = string_from_symbol_path(arg->value->type->path);
          LOG_NORMAL(state->log_out,
            "Cannot instantiate value '%s' of type '%s' because the variable has type '%s'.\n",
            value_str, src_type, arg_type);
          free(value_str);
          free(src_type);
          free(arg_type);
          return NULL;
        }
        return copy_value(arg->value);
      }
      break;
    case ValueTypeComposition:
      {
        Value *dst = malloc(sizeof(Value));
        dst->type = src->type;
        dst->value_type = ValueTypeComposition;
        dst->expression = src->expression;
        ARRAY_INIT(dst->arguments, struct Value);
        for (size_t i = 0; i < ARRAY_LENGTH(src->arguments); ++i)
        {
          const Value *arg = *ARRAY_GET(src->arguments, struct Value *, i);
          ARRAY_APPEND(dst->arguments, Value *,
            instantiate_value(state, arg, args));
        }
        return dst;
      }
      break;
  }
  return 0;
}

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

  ARRAY_INIT(value->arguments, Value *);
  for (Value * const *arg = args;
    *arg != NULL; ++arg)
  {
    ARRAY_APPEND(value->arguments, Value *, copy_value(*arg));
  }

  /* Make sure that the arguments match the types of the parameters of
     the expression. */
  if (ARRAY_LENGTH(value->arguments) !=
    ARRAY_LENGTH(value->expression->parameters))
  {
    char *expr_str = string_from_symbol_path(expr_path);
    LOG_NORMAL(state->log_out,
      "Cannot create value because the wrong number of arguments are supplied to the expression '%s'\n",
      expr_str);
    free(expr_str);
    free_value(value);
    return NULL;
  }
  Array args_array;
  ARRAY_INIT(args_array, struct Argument);
  for (size_t i = 0; i < ARRAY_LENGTH(value->arguments); ++i)
  {
    Value *arg = *ARRAY_GET(value->arguments, Value *, i);
    const struct Parameter *param =
      ARRAY_GET(value->expression->parameters, struct Parameter, i);
    struct Argument argument;
    argument.name = strdup(param->name);
    argument.value = copy_value(arg);
    ARRAY_APPEND(args_array, struct Argument, argument);
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
  for (size_t i = 0; i < ARRAY_LENGTH(value->expression->bindings); ++i)
  {
    const Value *binding = *ARRAY_GET(value->expression->bindings, Value *, i);
    Value *instantiated = instantiate_value(state, binding, args_array);

    Array occurrences;
    ARRAY_INIT(occurrences, Value *);
    enumerate_value_occurrences(instantiated, value, &occurrences);
    for (size_t j = 0; j < ARRAY_LENGTH(occurrences); ++j)
    {
      Value *occurrence = *ARRAY_GET(occurrences, Value *, j);
      occurrence->bound = TRUE;
    }
    ARRAY_FREE(occurrences);

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
  ARRAY_INIT(a->parameters, struct Parameter);
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
    ARRAY_APPEND(a->parameters, struct Parameter, p);
  }

  /* Requirements. */
  ARRAY_INIT(a->requirements, struct Requirement);
  for (struct PrototypeRequirement **req = proto.requirements;
    *req != NULL; ++req)
  {
    struct Requirement requirement;

    ARRAY_INIT(requirement.arguments, Value *);
    for (Value **arg = (*req)->arguments; *arg != NULL; ++arg)
    {
      ARRAY_APPEND(requirement.arguments, Value *, copy_value(*arg));
    }

    /* Make sure that the number of arguments match the type. */
    /* TODO: make validation of requirements its own function. */

    if (strcmp((*req)->require, "free_for") == 0)
    {
      requirement.type = RequirementTypeFreeFor;
      if (ARRAY_LENGTH(requirement.arguments) != 3)
        return LogicErrorSymbolAlreadyExists;
    }
    else if (strcmp((*req)->require, "not_free") == 0)
    {
      requirement.type = RequirementTypeNotFree;
      if (ARRAY_LENGTH(requirement.arguments) != 2)
        return LogicErrorSymbolAlreadyExists;
    }
    else if (strcmp((*req)->require, "substitution") == 0)
    {
      requirement.type = RequirementTypeSubstitution;
      if (ARRAY_LENGTH(requirement.arguments) != 4)
        return LogicErrorSymbolAlreadyExists;
    }
    else if (strcmp((*req)->require, "full_substitution") == 0)
    {
      requirement.type = RequirementTypeFullSubstitution;
      if (ARRAY_LENGTH(requirement.arguments) != 4)
        return LogicErrorSymbolAlreadyExists;
    }
    else
    {
      /* TODO: just ignore this requirement? */
      continue;
    }

    ARRAY_APPEND(a->requirements, struct Requirement, requirement);
  }

  /* Assumptions & inferences. */
  ARRAY_INIT(a->assumptions, struct Value *);
  ARRAY_INIT(a->inferences, struct Value *);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARRAY_APPEND(a->assumptions, struct Value *, copy_value(*assume));
  }
  for (Value **infer = proto.inferences;
    *infer != NULL; ++infer)
  {
    ARRAY_APPEND(a->inferences, struct Value *, copy_value(*infer));
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
    for (size_t i = 0; i < ARRAY_LENGTH(a->assumptions); ++i)
    {
      char *str = string_from_value(*ARRAY_GET(a->assumptions,
        struct Value *, i));
      printf("Assumption %zu: %s\n", i, str);
      free(str);
    }
    for (size_t i = 0; i < ARRAY_LENGTH(a->inferences); ++i)
    {
      char *str = string_from_value(*ARRAY_GET(a->inferences,
        struct Value *, i));
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
statement_proven(const Value *statement, Array proven)
{
  for (size_t i = 0; i < ARRAY_LENGTH(proven); ++i)
  {
    const Value *s = *ARRAY_GET(proven, Value *, i);
    if (values_equal(statement, s))
      return TRUE;
  }
  return FALSE;
}

static void
make_substitution_in_place(const Value *source, const Value *target,
  Value *context)
{
  if (values_equal(target, context))
  {
    copy_value_to(context, source);
  }
  else if (context->value_type == ValueTypeComposition)
  {
    for (size_t i = 0; i < ARRAY_LENGTH(context->arguments); ++i)
    {
      Value *arg = *ARRAY_GET(context->arguments, Value *, i);
        make_substitution_in_place(source, target, arg);
    }
  }
}

static bool
new_bindings_exist(LogicState *state, const Value *context)
{
  if (context->value_type == ValueTypeComposition)
  {
    Array args_array;
    ARRAY_INIT(args_array, struct Argument);
    for (size_t i = 0; i < ARRAY_LENGTH(context->arguments); ++i)
    {
      Value *arg = *ARRAY_GET(context->arguments, Value *, i);
      bool child_binds = new_bindings_exist(state, arg);
      if (child_binds)
        return TRUE;

      const struct Parameter *param =
        ARRAY_GET(context->expression->parameters, struct Parameter, i);
      struct Argument argument;
      argument.name = strdup(param->name);
      argument.value = copy_value(arg);
      ARRAY_APPEND(args_array, struct Argument, argument);
    }

    /* Look for things to bind. */
    for (size_t i = 0; i < ARRAY_LENGTH(context->expression->bindings); ++i)
    {
      const Value *binding =
        *ARRAY_GET(context->expression->bindings, Value *, i);
      Value *instantiated = instantiate_value(state, binding, args_array);

      Array occurrences;
      ARRAY_INIT(occurrences, Value *);
      enumerate_value_occurrences(instantiated, context, &occurrences);
      for (size_t j = 0; j < ARRAY_LENGTH(occurrences); ++j)
      {
        Value *occurrence = *ARRAY_GET(occurrences, Value *, j);
        if (occurrence->bound == FALSE)
          return TRUE;
      }
      ARRAY_FREE(occurrences);

      free_value(instantiated);
    }
  }
  return FALSE;
}

static bool
substitution_is_binding(LogicState *state, const Value *source,
  const Value *target, const Value *context)
{
  Value *ctx = copy_value(context);

  /* Make the substitution in place. Then traverse the tree, and at each
     composition node, try to make new bindings. */
  make_substitution_in_place(source, target, ctx);

  return new_bindings_exist(state, ctx);
}

static bool
evaluate_free_for(struct LogicState *state,
  const Value *source, const Value *target, const Value *context)
{
  /* Special case: anything is always free for itself. */
  if (values_equal(source, target))
    return TRUE;

  /* TODO: Instead of requiring everything to be terminal, in cases that
     we have non-terminals, figure out what must be required in order to
     make it work and check for that requirement in the environment. */
  if (!value_terminal(source) || !value_terminal(target)
    || !value_terminal(context))
    return FALSE;

  return !substitution_is_binding(state, source, target, context);
}

static bool
evaluate_not_free(struct LogicState *state,
  const Value *target, const Value *context)
{
  /* TODO: Instead of requiring everything to be terminal, in cases that
     we have non-terminals, figure out what must be required in order to
     make it work and check for that requirement in the environment. */
  if (!value_terminal(target) || !value_terminal(context))
    return FALSE;

  bool not_free = TRUE;
  Array occurrences;
  ARRAY_INIT(occurrences, const Value *);
  enumerate_value_occurrences(target, context, &occurrences);
  for (size_t i = 0; i < ARRAY_LENGTH(occurrences); ++i)
  {
    const Value *occurrence = *ARRAY_GET(occurrences, const Value *, i);
    if (!occurrence->bound)
      not_free = FALSE;
  }
  ARRAY_FREE(occurrences);

  return not_free;
}

static bool
is_substitution(const Value *target, const Value *context,
  const Value *source, const Value *new_context)
{
  if (values_equal(target, context))
  {
    if (values_equal(source, new_context))
      return TRUE;
    else if (values_equal(target, new_context))
      return TRUE;
    else
      return FALSE;
  }
  else if (context->value_type == ValueTypeComposition)
  {
    if (new_context->value_type != ValueTypeComposition)
      return FALSE;
    if (ARRAY_LENGTH(context->arguments) !=
      ARRAY_LENGTH(new_context->arguments))
      return FALSE;
    for (size_t i = 0; i < ARRAY_LENGTH(context->arguments); ++i)
    {
      const Value *ctx_arg = *ARRAY_GET(context->arguments, Value *, i);
      const Value *new_ctx_arg =
        *ARRAY_GET(new_context->arguments, Value *, i);
      if (!is_substitution(target, ctx_arg, source, new_ctx_arg))
        return FALSE;
    }
    return TRUE;
  }
  else
  {
    if (values_equal(context, new_context))
      return TRUE;
    else
      return FALSE;
  }
}

static bool
evaluate_substitution(struct LogicState *state,
  const Value *target, const Value *context,
  const Value *source, const Value *new_context)
{
  /* As a special case that doesn't (and cannot) require evaluation,
     always return true when performing the identity substitution. */
  if (values_equal(target, source) && values_equal(context, new_context))
    return TRUE;

  /* TODO: Instead of requiring everything to be terminal, in cases that
     we have non-terminals, figure out what must be required in order to
     make it work and check for that requirement in the environment. */
  if (!value_terminal(target) || !value_terminal(context)
    || !value_terminal(source) || !value_terminal(new_context))
    return FALSE;

  return is_substitution(target, context, source, new_context);
}

static bool
is_full_substitution(const Value *target, const Value *context,
  const Value *source, const Value *new_context)
{
  if (values_equal(target, context))
  {
    if (values_equal(source, new_context))
      return TRUE;
    else
      return FALSE;
  }
  else if (context->value_type == ValueTypeComposition)
  {
    if (new_context->value_type != ValueTypeComposition)
      return FALSE;
    if (ARRAY_LENGTH(context->arguments) !=
      ARRAY_LENGTH(new_context->arguments))
      return FALSE;
    for (size_t i = 0; i < ARRAY_LENGTH(context->arguments); ++i)
    {
      const Value *ctx_arg = *ARRAY_GET(context->arguments, Value *, i);
      const Value *new_ctx_arg =
        *ARRAY_GET(new_context->arguments, Value *, i);
      if (!is_full_substitution(target, ctx_arg, source, new_ctx_arg))
        return FALSE;
    }
    return TRUE;
  }
  else
  {
    if (values_equal(context, new_context))
      return TRUE;
    else
      return FALSE;
  }
}

static bool
evaluate_full_substitution(struct LogicState *state,
  const Value *target, const Value *context,
  const Value *source, const Value *new_context)
{
  /* As a special case that doesn't (and cannot) require evaluation,
     always return true when performing the identity substitution. */
  if (values_equal(target, source) && values_equal(context, new_context))
    return TRUE;

  /* TODO: Instead of requiring everything to be terminal, in cases that
     we have non-terminals, figure out what must be required in order to
     make it work and check for that requirement in the environment. */
  if (!value_terminal(target) || !value_terminal(context)
    || !value_terminal(source) || !value_terminal(new_context))
    return FALSE;

  return is_substitution(target, context, source, new_context);
}

static int
instantiate_theorem(struct LogicState *state,
  const struct Theorem *src, Array args, Array *proven)
{
  /* Check the requirements. */
  for (size_t i = 0; i < ARRAY_LENGTH(src->requirements); ++i)
  {
    bool satisfied = FALSE;
    const struct Requirement *req =
      ARRAY_GET(src->requirements, struct Requirement, i);

    Array instantiated_args;
    ARRAY_INIT(instantiated_args, Value *);
    for (size_t j = 0; j < ARRAY_LENGTH(req->arguments); ++j)
    {
      const Value *arg = *ARRAY_GET(req->arguments, Value *, j);
      Value *instantiated = instantiate_value(state, arg, args);
      ARRAY_APPEND(instantiated_args, Value *, instantiated);
    }

    switch (req->type)
    {
      case RequirementTypeFreeFor:
        {
          if (ARRAY_LENGTH(instantiated_args) != 3)
          {
            LOG_NORMAL(state->log_out,
              "Requirement has wrong number of arguments");
            return 1;
          }
          const Value *source = *ARRAY_GET(instantiated_args, Value *, 0);
          const Value *target = *ARRAY_GET(instantiated_args, Value *, 1);
          const Value *context = *ARRAY_GET(instantiated_args, Value *, 2);
          satisfied = evaluate_free_for(state, source, target, context);
        }
        break;
      case RequirementTypeNotFree:
        {
          if (ARRAY_LENGTH(instantiated_args) != 2)
          {
            LOG_NORMAL(state->log_out,
              "Requirement has wrong number of arguments");
            return 1;
          }
          const Value *target = *ARRAY_GET(instantiated_args, Value *, 0);
          const Value *context = *ARRAY_GET(instantiated_args, Value *, 1);
          satisfied = evaluate_not_free(state, target, context);
        }
        break;
      case RequirementTypeSubstitution:
        {
          if (ARRAY_LENGTH(instantiated_args) != 4)
          {
            LOG_NORMAL(state->log_out,
              "Requirement has wrong number of arguments");
            return 1;
          }
          const Value *target = *ARRAY_GET(instantiated_args, Value *, 0);
          const Value *context = *ARRAY_GET(instantiated_args, Value *, 1);
          const Value *source = *ARRAY_GET(instantiated_args, Value *, 2);
          const Value *new_context = *ARRAY_GET(instantiated_args, Value *, 3);
          satisfied = evaluate_substitution(state, target, context,
            source, new_context);
        }
        break;
      case RequirementTypeFullSubstitution:
        {
          if (ARRAY_LENGTH(instantiated_args) != 4)
          {
            LOG_NORMAL(state->log_out,
              "Requirement has wrong number of arguments");
            return 1;
          }
          const Value *target = *ARRAY_GET(instantiated_args, Value *, 0);
          const Value *context = *ARRAY_GET(instantiated_args, Value *, 1);
          const Value *source = *ARRAY_GET(instantiated_args, Value *, 2);
          const Value *new_context = *ARRAY_GET(instantiated_args, Value *, 3);
          satisfied = evaluate_full_substitution(state, target, context,
            source, new_context);
        }
        break;
    }

    if (!satisfied)
      return 1;
  }

  /* First, instantiate the assumptions. */
  Array instantiated_assumptions;
  ARRAY_INIT(instantiated_assumptions, Value *);
  for (size_t i = 0; i < ARRAY_LENGTH(src->assumptions); ++i)
  {
    const Value *assumption = *ARRAY_GET(src->assumptions, Value *, i);
    Value *instantiated = instantiate_value(state, assumption, args);
    if (instantiated == NULL)
      return 1;
    ARRAY_APPEND(instantiated_assumptions, Value *, instantiated);
  }

  /* Verify that each assumption has been proven. */
  for (size_t i = 0; i < ARRAY_LENGTH(instantiated_assumptions); ++i)
  {
    Value *assumption = *ARRAY_GET(instantiated_assumptions, Value *, i);
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
  ARRAY_FREE(instantiated_assumptions);

  /* Add all the inferences to the environment as proven statements. */
  for (size_t i = 0; i < ARRAY_LENGTH(src->inferences); ++i)
  {
    const Value *inference = *ARRAY_GET(src->inferences, Value *, i);
    Value *instantiated = instantiate_value(state, inference, args);
    if (instantiated == NULL)
      return 1;
    ARRAY_APPEND(*proven, Value *, instantiated);
  }

  return 0;
}

static void
list_proven(LogicState *state, Array proven)
{
  LOG_NORMAL(state->log_out, "Statements proven:\n");
  for (size_t i = 0; i < ARRAY_LENGTH(proven); ++i)
  {
    Value *stmt = *ARRAY_GET(proven, Value *, i);
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
  ARRAY_INIT(a->parameters, struct Parameter);
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
    ARRAY_APPEND(a->parameters, struct Parameter, p);
  }

  ARRAY_INIT(a->requirements, struct Requirement);

  /* Assumptions & inferences. */
  ARRAY_INIT(a->assumptions, struct Value *);
  ARRAY_INIT(a->inferences, struct Value *);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARRAY_APPEND(a->assumptions, struct Value *, copy_value(*assume));
  }
  for (Value **infer = proto.inferences;
    *infer != NULL; ++infer)
  {
    ARRAY_APPEND(a->inferences, struct Value *, copy_value(*infer));
  }

  /* Finally, check the proof. */
  Array proven;
  ARRAY_INIT(proven, Value *);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARRAY_APPEND(proven, struct Value *, copy_value(*assume));
  }
  for (struct PrototypeProofStep **step = proto.steps;
    *step != NULL; ++step)
  {
    const struct Symbol *thm_symbol = locate_symbol_with_type(state,
      (*step)->theorem_path, SymbolTypeTheorem);
    if (thm_symbol == NULL)
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced in proof does not exist.\n");
      return LogicErrorSymbolAlreadyExists;
    }
    struct Theorem *thm = (struct Theorem *)thm_symbol->object;

    /* Build a list of arguments. */
    size_t args_n = 0;
    for (Value **arg = (*step)->arguments; *arg != NULL; ++arg)
      ++args_n;
    if (args_n != ARRAY_LENGTH(thm->parameters))
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced received the wrong number of arguments.\n");
      return LogicErrorSymbolAlreadyExists;
    }

    Array args;
    ARRAY_INIT(args, struct Argument);
    for (size_t i = 0; i < args_n; ++i)
    {
      struct Parameter *param = ARRAY_GET(thm->parameters, struct Parameter, i);

      struct Argument arg;
      arg.name = strdup(param->name);
      arg.value = copy_value((*step)->arguments[i]);

      if (!types_equal(param->type, arg.value->type))
      {
        LOG_NORMAL(state->log_out,
          "Cannot add theorem because an axiom/theorem referenced received an argument with the wrong type.\n");
        return LogicErrorSymbolAlreadyExists;
      }

      ARRAY_APPEND(args, struct Argument, arg);
    }

    if (instantiate_theorem(state, thm, args, &proven) != 0)
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced could not be instantiated.\n");
      list_proven(state, proven);
      return LogicErrorSymbolAlreadyExists;
    }

    for (size_t i = 0; i < args_n; ++i)
    {
      struct Argument *arg = ARRAY_GET(args, struct Argument, i);
      free(arg->name);
      free_value(arg->value);
    }
    ARRAY_FREE(args);
  }

  /* Check that all the inferences have been proven. */
  for (size_t i = 0; i < ARRAY_LENGTH(a->inferences); ++i)
  {
    Value *infer = *ARRAY_GET(a->inferences, Value *, i);
    if (!statement_proven(infer, proven))
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an inference was not proven.\n");
      return LogicErrorSymbolAlreadyExists;
    }
  }

  /* Free all the statements that we've proven. */
  for (size_t i = 0; i < ARRAY_LENGTH(proven); ++i)
  {
    Value *v = *ARRAY_GET(proven, Value *, i);
    free_value(v);
  }
  ARRAY_FREE(proven);

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
    for (size_t i = 0; i < ARRAY_LENGTH(a->assumptions); ++i)
    {
      char *str = string_from_value(*ARRAY_GET(a->assumptions,
        struct Value *, i));
      printf("Assumption %zu: %s\n", i, str);
      free(str);
    }
    for (size_t i = 0; i < ARRAY_LENGTH(a->inferences); ++i)
    {
      char *str = string_from_value(*ARRAY_GET(a->inferences,
        struct Value *, i));
      printf("Inference %zu: %s\n", i, str);
      free(str);
    }
    /*expr_str = string_from_expression(e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);*/
  }

  return LogicErrorNone;
}
