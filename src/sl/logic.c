#include "logic.h"
#include <string.h>

struct SymbolPath
{
  Array segments;
};

struct Parameter
{
  char *name;
  const struct Type *type;
};

struct Type
{
  uint32_t id;
  //bool atomic;
};

struct Expression
{
  uint32_t id;
  const struct Type *type;
  Array parameters;
};

enum SymbolType
{
  SymbolTypeType,
  SymbolTypeExpression,
  SymbolTypeTheorem
};

struct Symbol
{
  SymbolPath *path;
  enum SymbolType type;
  void *object;
};

struct LogicState
{
  Array symbol_table;
  uint32_t next_id;
};

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
  for (size_t i = 0; ARRAY_LENGTH(expr->parameters); ++i)
  {
    struct Parameter *param =
      ARRAY_GET(expr->parameters, struct Parameter, i);
    free_parameter(param);
  }
  ARRAY_FREE(expr->parameters);
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
      break;
  }
  free(sym->object);
}

/* Core Logic */
LogicState *
new_logic_state()
{
  LogicState *state = malloc(sizeof(LogicState));
  ARRAY_INIT(state->symbol_table, struct Symbol);
  state->next_id = 0;
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
add_type(LogicState *state, const SymbolPath *type)
{
  if (locate_symbol(state, type) != NULL)
  {
    return LogicErrorSymbolAlreadyExists;
  }

  struct Type *t = malloc(sizeof(struct Type));
  t->id = state->next_id;
  ++state->next_id;
  //t->atomic = atomic;

  struct Symbol sym;
  sym.path = copy_symbol_path(type);
  sym.type = SymbolTypeType;
  sym.object = t;

  add_symbol(state, sym);

  return LogicErrorNone;
}

LogicError
add_expression(LogicState *state, struct PrototypeExpression proto)
{
  if (locate_symbol(state, proto.expression_path) != NULL)
  {
    return LogicErrorSymbolAlreadyExists;
  }

  struct Symbol *expression_type =
    locate_symbol_with_type(state, proto.expression_type, SymbolTypeType);
  if (expression_type == NULL)
    return LogicErrorSymbolAlreadyExists;

  for (const struct PrototypeParameter *param = proto.parameters;
    *param != NULL; ++param)
  {
    
  }

  struct Expression *e = malloc(sizeof(struct Expression));
  e->id = state->next_id;
  ++state->next_id;

  struct Symbol sym;
  sym.path = copy_symbol_path(proto.expression_path);
  sym.type = SymbolTypeExpression;
  sym.object = e;

  add_symbol(state, sym);

  return LogicErrorNone;
}

#if 0
struct ObjectType
{
  char *typename;
};

struct Parameter
{
  char *name;
  const ObjectType *type;
};

struct ObjectExpression
{
  char *name;
  const struct ObjectType *type;
  Array parameters;
};

struct Value
{
  char *name;
  enum ValueType type;
  const struct ObjectType *object_type;
  Array arguments;
};

struct ObjectTheorem
{
  char *name;
  Array parameters;

  Array assumptions;
  Array inferences;
};

struct Symbol
{
  SymbolPath path;
  enum SymbolType type;
  void *object;
};

bool
types_equal(const ObjectType *a, const ObjectType *b)
{
  if (strcmp(a->typename, b->typename) == 0)
    return TRUE;
  return FALSE;
}

void
free_type(ObjectType *type)
{
  free(type->typename);
}

Parameter *
copy_parameter(const Parameter *src)
{
  Parameter *dst = malloc(sizeof(Parameter));
  dst->name = strdup(src->name);
  dst->type = src->type;
  return dst;
}

void
free_parameter(Parameter *param)
{
  free(param->name);
}

void
free_expression(ObjectExpression *expr)
{
  free(expr->name);
  for (size_t i = 0; i < ARRAY_LENGTH(expr->parameters); ++i)
  {
    struct Parameter *param = ARRAY_GET(expr->parameters, struct Parameter, i);
    free_parameter(param);
  }
  ARRAY_FREE(expr->parameters);
}

bool
values_equal(const Value *a, const Value *b)
{
  if (strcmp(a->name, b->name) != 0)
    return FALSE;
  if (a->type != b->type)
    return FALSE;
  if (!types_equal(a->object_type, b->object_type))
    return FALSE;
  if (a->type == ValueTypeComposition)
  {
    if (ARRAY_LENGTH(a->arguments) != ARRAY_LENGTH(b->arguments))
      return FALSE;
    for (size_t i = 0; i < ARRAY_LENGTH(a->arguments); ++i)
    {
      const struct Value *arg_a =
        ARRAY_GET(a->arguments, struct Value, i);
      const struct Value *arg_b =
        ARRAY_GET(b->arguments, struct Value, i);
      if (!values_equal(arg_a, arg_b))
        return FALSE;
    }
  }
  return TRUE;
}

char *
string_from_value(const Value *value)
{
  switch (value->type)
  {
    case ValueTypeComposition:
      {
        if (ARRAY_LENGTH(value->arguments) == 0)
        {
          size_t len = 3 + strlen(value->name);
          char *str = malloc(len);
          char *c = str;
          strcpy(c, value->name);
          c += strlen(value->name);
          strcpy(c, "()");
          c += 2;
          *c = '\0';
          return str;
        }
        else
        {
          size_t len = 3 + strlen(value->name);
          char **args = malloc(sizeof(char *) * ARRAY_LENGTH(value->arguments));
          for (size_t i = 0; i < ARRAY_LENGTH(value->arguments); ++i)
          {
            const struct Value *arg =
              ARRAY_GET(value->arguments, struct Value, i);
            args[i] = string_from_value(arg);
            len += strlen(args[i]);
          }
          len += (ARRAY_LENGTH(value->arguments) - 1) * 2;

          char *str = malloc(len);
          char *c = str;
          strcpy(c, value->name);
          c += strlen(value->name);
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

          return str;
        }
      }
      break;
    case ValueTypeConstant:
      {
        size_t len = 1 + strlen(value->name);
        char *str = malloc(len);
        char *c = str;
        strcpy(c, value->name);
        c += strlen(value->name);
        *c = '\0';
        return str;
      }
      break;
    case ValueTypeVariable:
      {
        size_t len = 2 + strlen(value->name);
        char *str = malloc(len);
        char *c = str;
        *c = '$';
        ++c;
        strcpy(c, value->name);
        c += strlen(value->name);
        *c = '\0';
        return str;
      }
      break;
  }
}

static void
copy_value_to(Value *dst, const Value *src)
{
  dst->name = strdup(src->name);
  dst->type = src->type;
  dst->object_type = src->object_type;
  if (src->type == ValueTypeComposition)
  {
    ARRAY_INIT(dst->arguments, struct Value);
    for (size_t i = 0; i < ARRAY_LENGTH(src->arguments); ++i)
    {
      const struct Value *arg =
        ARRAY_GET(src->arguments, struct Value, i);
      struct Value copy;
      copy_value_to(&copy, arg);
      ARRAY_APPEND(dst->arguments, struct Value, copy);
    }
  }
}

Value *
copy_value(const Value *src)
{
  Value *dst = malloc(sizeof(Value));
  copy_value_to(dst, src);
  return dst;
}

void
free_value(Value *value)
{
  free(value->name);
  if (value->type == ValueTypeComposition)
  {
    for (size_t i = 0; i < ARRAY_LENGTH(value->arguments); ++i)
    {
      struct Value *arg = ARRAY_GET(value->arguments, struct Value, i);
      free_value(arg);
    }
    ARRAY_FREE(value->arguments);
  }
}

void
free_theorem(ObjectTheorem *theorem)
{
  free(theorem->name);

  for (size_t i = 0; i < ARRAY_LENGTH(theorem->parameters); ++i)
  {
    struct Parameter *param =
      ARRAY_GET(theorem->parameters, struct Parameter, i);
    free_parameter(param);
  }
  ARRAY_FREE(theorem->parameters);

  for (size_t i = 0; i < ARRAY_LENGTH(theorem->assumptions); ++i)
  {
    struct Value *assumption = ARRAY_GET(theorem->assumptions, struct Value, i);
    free_value(assumption);
  }
  ARRAY_FREE(theorem->assumptions);

  for (size_t i = 0; i < ARRAY_LENGTH(theorem->inferences); ++i)
  {
    struct Value *inference = ARRAY_GET(theorem->inferences, struct Value, i);
    free_value(inference);
  }
  ARRAY_FREE(theorem->inferences);
}

void
free_symbol(Symbol *sym)
{
  free_symbol_path(&sym->path);
  switch (sym->type)
  {
    case SymbolTypeType:
      free_type(sym->object);
      break;
    case SymbolTypeExpression:
      free_expression(sym->object);
      break;
    case SymbolTypeTheorem:
      free_theorem(sym->object);
      break;
    default:
      break;
  }
  free(sym->object);
}
#endif
