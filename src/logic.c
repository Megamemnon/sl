#include "logic.h"
#include "parse.h"
#include <string.h>

#include "core.h"

static uint32_t logic_state_add_string(sl_LogicState *state, const char *str)
{
  uint32_t index;
  if (state == NULL || str == NULL)
    return 0;
  /* TODO: binary search with alphabetical order? */
  for (size_t i = 0; i < ARR_LENGTH(state->string_table); ++i) {
    const char *stored = *ARR_GET(state->string_table, i);
    if (strcmp(str, stored) == 0)
      return i;
  }
  index = ARR_LENGTH(state->string_table);
  ARR_APPEND(state->string_table, strdup(str));
  return index;
}

const char * logic_state_get_string(const sl_LogicState *state, uint32_t index)
{
  if (state == NULL)
    return NULL;
  if (index >= ARR_LENGTH(state->string_table))
    return NULL;
  return *ARR_GET(state->string_table, index);
}

/* Paths */
sl_SymbolPath *
sl_new_symbol_path()
{
  sl_SymbolPath *path = SL_NEW(sl_SymbolPath);
  ARR_INIT(path->segments);
  return path;
}

sl_SymbolPath *
sl_copy_symbol_path(const sl_SymbolPath *src)
{
  sl_SymbolPath *dst = sl_new_symbol_path();
  for (size_t i = 0; i < ARR_LENGTH(src->segments); ++i)
  {
    ARR_APPEND(dst->segments, *ARR_GET(src->segments, i));
  }
  return dst;
}

void
sl_free_symbol_path(sl_SymbolPath *path)
{
  ARR_FREE(path->segments);
  free(path);
}

int
sl_get_symbol_path_length(const sl_SymbolPath *path)
{
  return ARR_LENGTH(path->segments);
}

const char *
sl_get_symbol_path_segment(const sl_LogicState *state,
  const sl_SymbolPath *path, size_t index)
{
  return logic_state_get_string(state, *ARR_GET(path->segments, index));
}

const char *
sl_get_symbol_path_last_segment(const sl_LogicState *state,
  const sl_SymbolPath *path)
{
  return sl_get_symbol_path_segment(state, path,
    sl_get_symbol_path_length(path) - 1);
}

char *
sl_string_from_symbol_path(const sl_LogicState *state,
  const sl_SymbolPath *path)
{
  if (ARR_LENGTH(path->segments) == 0)
    return strdup("");
  size_t str_len = ARR_LENGTH(path->segments);
  for (size_t i = 0; i < ARR_LENGTH(path->segments); ++i)
  {
    const char *segment = sl_get_symbol_path_segment(state, path, i);
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
    const char *segment = sl_get_symbol_path_segment(state, path, i);
    strcpy(c, segment);
    c += strlen(segment);
  }
  *c = '\0';
  return str;
}

void
sl_push_symbol_path(sl_LogicState *state, sl_SymbolPath *path,
  const char *segment)
{
  uint32_t index;
  index = logic_state_add_string(state, segment);
  ARR_APPEND(path->segments, index);
}

void
sl_pop_symbol_path(sl_SymbolPath *path)
{
  ARR_POP(path->segments);
}

void
sl_append_symbol_path(sl_SymbolPath *path, const sl_SymbolPath *to_append)
{
  /* TODO: reserve segments before. */
  for (size_t i = 0; i < ARR_LENGTH(to_append->segments); ++i)
  {
    uint32_t segment = *ARR_GET(to_append->segments, i);
    ARR_APPEND(path->segments, segment);
  }
}

bool
sl_symbol_paths_equal(const sl_SymbolPath *a, const sl_SymbolPath *b)
{
  if (ARR_LENGTH(a->segments) != ARR_LENGTH(b->segments))
    return FALSE;
  for (size_t i = 0; i < ARR_LENGTH(a->segments); ++i)
  {
    uint32_t a_segment = *ARR_GET(a->segments, i);
    uint32_t b_segment = *ARR_GET(b->segments, i);
    if (a_segment != b_segment)
      return FALSE;
  }
  return TRUE;
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
  ARR_FREE(expr->parameters);
  for (size_t i = 0; i < ARR_LENGTH(expr->bindings); ++i)
  {
    Value *binding = *ARR_GET(expr->bindings, i);
    free_value(binding);
  }
  ARR_FREE(expr->bindings);
  if (expr->has_latex) {
    for (size_t i = 0; i < ARR_LENGTH(expr->latex.segments); ++i) {
      struct LatexFormatSegment *seg;
      seg = ARR_GET(expr->latex.segments, i);
      free(seg->string);
    }
    ARR_FREE(expr->latex.segments);
  }
  if (expr->replace_with != NULL)
    free_value(expr->replace_with);
}

static char *
string_from_expression(const sl_LogicState *state,
  const struct Expression *expr)
{
  size_t len = 5; /* two pairs of parentheses "()" and terminator. */
  char *path = sl_string_from_symbol_path(state, expr->path);
  const sl_SymbolPath *type_path =
      sl_logic_get_symbol_path_by_id(state, expr->type_id);
  char *type = sl_string_from_symbol_path(state, type_path);
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
      const sl_SymbolPath *type_path =
          sl_logic_get_symbol_path_by_id(state, param->type_id);
      const char *param_name = logic_state_get_string(state, param->name_id);
      char *param_type = sl_string_from_symbol_path(state, type_path);
      len += strlen(param_name) + strlen(param_type) + 3; /* '[NAME] : [TYPE]' */
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
      const sl_SymbolPath *type_path =
          sl_logic_get_symbol_path_by_id(state, param->type_id);
      const char *param_name = logic_state_get_string(state, param->name_id);
      strcpy(c, param_name);
      c += strlen(param_name);
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

static void
free_constant(struct Constant *c)
{
  if (c->latex_format != NULL)
    free(c->latex_format);
}

/* Theorems. */
static void
free_theorem(struct Theorem *thm)
{
  ARR_FREE(thm->parameters);

  for (size_t i = 0; i < ARR_LENGTH(thm->requirements); ++i) {
    struct Requirement *req = ARR_GET(thm->requirements, i);
    for (size_t j = 0; j < ARR_LENGTH(req->arguments); ++j) {
      Value *arg = *ARR_GET(req->arguments, j);
      free_value(arg);
    }
    ARR_FREE(req->arguments);
  }
  ARR_FREE(thm->requirements);

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

  if (!thm->is_axiom) {
    for (size_t i = 0; i < ARR_LENGTH(thm->steps); ++i) {
      struct TheoremReference *step = ARR_GET(thm->steps, i);
      for (size_t j = 0; j < ARR_LENGTH(step->arguments); ++j) {
        Value *arg = *ARR_GET(step->arguments, j);
        free_value(arg);
      }
      ARR_FREE(step->arguments);
    }
    ARR_FREE(thm->steps);
  }
}

/* Symbols */
static void
free_symbol(sl_LogicSymbol *sym)
{
  if (sym == NULL)
    return;
  sl_free_symbol_path(sym->path);
  switch (sym->type)
  {
    case sl_LogicSymbolType_Type:
      free_type((struct Type *)sym->object);
      break;
    case sl_LogicSymbolType_Constant:
      free_constant((struct Constant *)sym->object);
      break;
    case sl_LogicSymbolType_Expression:
      free_expression((struct Expression *)sym->object);
      break;
    case sl_LogicSymbolType_Theorem:
      free_theorem((struct Theorem *)sym->object);
      break;
  }
  free(sym->object);
}

/* Core Logic */
sl_LogicState *
sl_new_logic_state(FILE *log_out)
{
  sl_LogicState *state = SL_NEW(sl_LogicState);
  if (state == NULL)
    return NULL;
  ARR_INIT(state->string_table);
  ARR_INIT(state->symbol_table);
  state->next_id = 0;
  state->log_out = log_out;
  {
    sl_SymbolPath *base = sl_new_symbol_path();
    sl_logic_make_namespace(state, base);
    sl_free_symbol_path(base);
  }
  return state;
}

void
sl_free_logic_state(sl_LogicState *state)
{
  for (size_t i = 0; i < ARR_LENGTH(state->string_table); ++i) {
    char *str = *ARR_GET(state->string_table, i);
    free(str);
  }
  ARR_FREE(state->string_table);
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    free_symbol(sym);
  }
  ARR_FREE(state->symbol_table);
  free(state);
}

sl_LogicSymbol *
sl_logic_get_symbol(sl_LogicState *state, const sl_SymbolPath *path)
{
  /* TODO: Optimize. */
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    if (sl_symbol_paths_equal(sym->path, path))
      return sym;
  }
  return NULL;
}

sl_LogicSymbolType
sl_get_symbol_type(const sl_LogicSymbol *symbol)
{
  return symbol->type;
}

size_t sl_logic_count_symbols(const sl_LogicState *state)
{
  return ARR_LENGTH(state->symbol_table);
}

size_t sl_logic_count_symbols_of_type(const sl_LogicState *state,
    sl_LogicSymbolType type)
{
  size_t count = 0;
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i) {
    const sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    if (sym->type == type)
      count += 1;
  }
  return count;
}

bool
logic_state_path_occupied(const sl_LogicState *state, const sl_SymbolPath *path)
{
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    if (sl_symbol_paths_equal(sym->path, path))
      return TRUE;
  }
  return FALSE;
}

sl_SymbolPath *
find_first_occupied_path(const sl_LogicState *state, sl_SymbolPath **paths)
{
  for (sl_SymbolPath **path = paths; *path != NULL; ++path)
  {
    if (logic_state_path_occupied(state, *path))
      return sl_copy_symbol_path(*path);
  }
  return NULL;
}

static sl_LogicSymbol *
locate_symbol(sl_LogicState *state, const sl_SymbolPath *path)
{
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    if (sl_symbol_paths_equal(sym->path, path))
      return sym;
  }
  return NULL;
}

static sl_LogicSymbol *
locate_symbol_with_type(sl_LogicState *state, const sl_SymbolPath *path,
  sl_LogicSymbolType type)
{
  sl_LogicSymbol *sym = locate_symbol(state, path);
  if (sym == NULL)
    return NULL;
  if (sym->type != type)
    return NULL;
  return sym;
}

sl_LogicError sl_logic_get_symbol_id(const sl_LogicState *state,
    const sl_SymbolPath *path, uint32_t *id)
{
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i) {
    sl_LogicSymbol *sym;
    sym = ARR_GET(state->symbol_table, i);
    if (sl_symbol_paths_equal(sym->path, path)) {
      *id = i;
      return sl_LogicError_None;
    }
  }
  return sl_LogicError_NoSymbol;
}

sl_LogicSymbol * sl_logic_get_symbol_by_id(sl_LogicState *state,
    uint32_t id)
{
  if (id >= ARR_LENGTH(state->symbol_table))
    return NULL;
  else
    return ARR_GET(state->symbol_table, id);
}

const sl_SymbolPath * sl_logic_get_symbol_path_by_id(
    const sl_LogicState *state, uint32_t id)
{
  if (id >= ARR_LENGTH(state->symbol_table)) {
    return NULL;
  } else {
    const sl_LogicSymbol *sym = ARR_GET(state->symbol_table, id);
    return sym->path;
  }
}

static sl_LogicError
add_symbol(sl_LogicState *state, sl_LogicSymbol sym)
{
  if (locate_symbol(state, sym.path) != NULL)
  {
    char *path_str;
    path_str = sl_string_from_symbol_path(state, sym.path);
    LOG_NORMAL(state->log_out,
      "Cannot add symbol '%s' because the path is in use.\n", path_str);
    free(path_str);
    return sl_LogicError_SymbolAlreadyExists;
  }
  else if (sl_get_symbol_path_length(sym.path) > 0)
  {
    sl_SymbolPath *parent_path;
    parent_path = sl_copy_symbol_path(sym.path);
    sl_pop_symbol_path(parent_path);
    if (locate_symbol_with_type(state, parent_path,
      sl_LogicSymbolType_Namespace) == NULL)
    {
      char *path_str, *parent_path_str;
      path_str = sl_string_from_symbol_path(state, sym.path);
      parent_path_str = sl_string_from_symbol_path(state, parent_path);
      LOG_NORMAL(state->log_out,
        "Cannot add symbol '%s' because there is no parent namespace '%s'.\n",
        path_str, parent_path_str);
      free(path_str);
      free(parent_path_str);
      sl_free_symbol_path(parent_path);
      return sl_LogicError_NoParent;
    }
    sl_free_symbol_path(parent_path);
  }
  ARR_APPEND(state->symbol_table, sym);
  return sl_LogicError_None;
}

sl_LogicError
sl_logic_make_namespace(sl_LogicState *state,
  const sl_SymbolPath *namespace_path)
{
  sl_LogicSymbol sym;
  sl_LogicError err;
  sym.path = sl_copy_symbol_path(namespace_path);
  sym.id = state->next_id++;
  sym.type = sl_LogicSymbolType_Namespace;
  sym.object = NULL;

  err = add_symbol(state, sym);
  if (err != sl_LogicError_None)
  {
    sl_free_symbol_path(sym.path);
    return err;
  }
  return sl_LogicError_None;
}

sl_LogicError sl_logic_make_type(sl_LogicState *state,
    const sl_SymbolPath *type_path, bool atomic, bool binds, bool dummies)
{
  struct Type *t;
  sl_LogicSymbol sym;
  sl_LogicError err;
  if (!atomic && binds) {
    char *type_str;
    type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out,
        "Cannot add type '%s' because it binds but is not atomic.\n",
        type_str);
    free(type_str);
    return sl_LogicError_CannotBindNonAtomic;
  }

  t = SL_NEW(struct Type);
  t->id = state->next_id++;
  t->atomic = atomic;
  t->binds = binds;
  t->dummies = dummies;
  sym.path = sl_copy_symbol_path(type_path);
  sym.type = sl_LogicSymbolType_Type;
  sym.object = t;
  t->path = sym.path;

  err = add_symbol(state, sym);
  if (err != sl_LogicError_None) {
    free(t);
    sl_free_symbol_path(sym.path);
    return err;
  } else {
    char *type_str;
    type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out, "Successfully added type '%s'.\n", type_str);
    free(type_str);
  }
  return sl_LogicError_None;
}

bool
types_equal(const struct Type *a, const struct Type *b)
{
  return (a->id == b->id) ? TRUE : FALSE;
}

sl_LogicError
sl_logic_make_constant(sl_LogicState *state, const sl_SymbolPath *constant_path,
  const sl_SymbolPath *type_path, const char *latex_format)
{
  uint32_t type_id;
  struct Constant *c;
  sl_LogicSymbol sym;
  sl_LogicError err;
  err = sl_logic_get_symbol_id(state, type_path,
      &type_id);
  if (err != sl_LogicError_None)
  {
    char *const_str, *type_str;
    const_str = sl_string_from_symbol_path(state, constant_path);
    type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out,
      "Cannot add constant '%s' because there is no such type '%s'.\n",
      const_str, type_str);
    free(const_str);
    free(type_str);
    return sl_LogicError_NoType;
  }

  c = SL_NEW(struct Constant);
  c->id = state->next_id++;
  c->type_id = type_id;
  if (latex_format != NULL)
    c->latex_format = strdup(latex_format);
  else
    c->latex_format = NULL;
  sym.path = sl_copy_symbol_path(constant_path);
  sym.type = sl_LogicSymbolType_Constant;
  sym.object = c;

  c->path = sym.path;

  err = add_symbol(state, sym);
  if (err != sl_LogicError_None)
  {
    free(c);
    sl_free_symbol_path(sym.path);
    return err;
  }
  else
  {
    char *const_str;
    const_str = sl_string_from_symbol_path(state, sym.path);
    LOG_NORMAL(state->log_out, "Successfully added constant '%s'.\n",
      const_str);
    free(const_str);
  }
  return sl_LogicError_None;
}

sl_LogicError
sl_logic_make_constspace(sl_LogicState *state,
  const sl_SymbolPath *constspace_path, const sl_SymbolPath *type_path)
{
  sl_LogicSymbol *type_symbol;
  struct Constspace *c;
  sl_LogicSymbol sym;
  uint32_t type_id;
  sl_LogicError err;
  err = sl_logic_get_symbol_id(state, type_path, &type_id);
  if (err != sl_LogicError_None)
  {
    char *constspace_str, *type_str;
    constspace_str = sl_string_from_symbol_path(state, constspace_path);
    type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out,
      "Cannot add constspace '%s' because there is no such type '%s'.\n",
      constspace_str, type_str);
    free(constspace_str);
    free(type_str);
    return sl_LogicError_NoType;
  }

  c = SL_NEW(struct Constspace);
  c->id = state->next_id++;
  c->type_id = type_id;
  sym.path = sl_copy_symbol_path(constspace_path);
  sym.type = sl_LogicSymbolType_Constspace;
  sym.object = c;

  err = add_symbol(state, sym);
  if (err != sl_LogicError_None)
  {
    free(c);
    sl_free_symbol_path(sym.path);
    return err;
  }
  else
  {
    char *constspace_str;
    constspace_str = sl_string_from_symbol_path(state, sym.path);
    LOG_NORMAL(state->log_out, "Successfully created constspace '%s'.\n",
      constspace_str);
    free(constspace_str);
  }
  return sl_LogicError_None;
}

sl_LogicError sl_logic_make_block(sl_LogicState *state,
    struct sl_PrototypeParameter **parameters, sl_ParametrizedBlock **block)
{
  size_t params_n = 0;
  if (state == NULL || parameters == NULL || block == NULL)
    return sl_LogicError_None;

  /* Verify the parameters. */
  for (struct sl_PrototypeParameter **_param = parameters; *_param != NULL;
      ++_param) {
    struct sl_PrototypeParameter *param;
    sl_LogicSymbol *type_symbol;
    param = *_param;
    /* Is this parameter repeated? */
    for (struct sl_PrototypeParameter **_param2 = parameters;
        _param2 != _param; ++_param2) {
      struct sl_PrototypeParameter *param2;
      param2 = *_param2;
      if (strcmp(param->name, param2->name) == 0) {
        LOG_NORMAL(state->log_out,
            "Couldn't create a parametrized block because the parameter '%s' was repeated.\n",
            param->name);
        return sl_LogicError_RepeatedParameter;
      }
    }
    type_symbol = locate_symbol_with_type(state, param->type_path,
        sl_LogicSymbolType_Type);
    if (type_symbol == NULL)
    {
      char *type_str;
      type_str = sl_string_from_symbol_path(state, param->type_path);
      LOG_NORMAL(state->log_out,
          "Couldn't create a parametrized block because the parameter '%s' refers to a nonexistent type '%s'.\n",
          param->name, type_str);
      free(type_str);
      return sl_LogicError_NoType;
    }
    params_n += 1;
  }

  /* After checking the validity of the parameters, go ahead and construct
     the block. */
  *block = SL_NEW(sl_ParametrizedBlock);
  if (*block == NULL)
    return sl_LogicError_Memory;
  ARR_INIT_RESERVE((*block)->parameters, params_n);
  for (struct sl_PrototypeParameter **_param = parameters; *_param != NULL;
      ++_param) {
    struct sl_PrototypeParameter *proto;
    sl_LogicSymbol *type_symbol;
    struct sl_Parameter param;
    proto = *_param;
    type_symbol = locate_symbol_with_type(state, proto->type_path,
        sl_LogicSymbolType_Type);
    param.name_id = logic_state_add_string(state, proto->name);
    param.type = (struct Type *)type_symbol->object;
    ARR_APPEND((*block)->parameters, param);
  }

  return sl_LogicError_None;
}

void sl_logic_free_block(sl_ParametrizedBlock *block)
{
  if (block == NULL)
    return;
  ARR_FREE(block->parameters);
  free(block);
}

sl_LogicError
add_expression(sl_LogicState *state, struct PrototypeExpression proto)
{
  uint32_t type_id;
  sl_LogicError err;
  if (locate_symbol(state, proto.expression_path) != NULL)
  {
    char *expr_str = sl_string_from_symbol_path(state, proto.expression_path);
    LOG_NORMAL(state->log_out,
      "Cannot add expression '%s' because the path is in use.\n", expr_str);
    free(expr_str);
    return sl_LogicError_SymbolAlreadyExists;
  }

  struct Expression *e = malloc(sizeof(struct Expression));
  e->id = state->next_id;
  ++state->next_id;

  sl_LogicSymbol *type_symbol = locate_symbol_with_type(state,
    proto.expression_type, sl_LogicSymbolType_Type);
  err = sl_logic_get_symbol_id(state, proto.expression_type, &type_id);
  if (err != sl_LogicError_None)
  {
    char *expr_str = sl_string_from_symbol_path(state, proto.expression_path);
    char *type_str = sl_string_from_symbol_path(state, proto.expression_type);
    LOG_NORMAL(state->log_out,
      "Cannot add expression '%s' because there is no such type '%s'.\n",
      expr_str, type_str);
    free(expr_str);
    free(type_str);
    free(e);
    return sl_LogicError_SymbolAlreadyExists;
  }
  e->type_id = type_id;
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
  {
    const sl_LogicSymbol *type_sym = sl_logic_get_symbol_by_id(state, type_id);
    const struct Type *type = (struct Type *)type_sym->object;
    if (type->atomic)
    {
      char *expr_str = sl_string_from_symbol_path(state, proto.expression_path);
      char *type_str = sl_string_from_symbol_path(state, proto.expression_type);
      LOG_NORMAL(state->log_out,
        "Cannot add expression '%s' because the type '%s' is atomic.\n",
        expr_str, type_str);
      free(expr_str);
      free(type_str);
      free(e);
      return sl_LogicError_SymbolAlreadyExists;
    }
  }

  ARR_INIT(e->parameters);
  for (struct PrototypeParameter **param = proto.parameters;
    *param != NULL; ++param)
  {
    struct Parameter p;
    uint32_t type_id;
    sl_LogicError err;
    err = sl_logic_get_symbol_id(state, (*param)->type, &type_id);
    if (err != sl_LogicError_None)
    {
      char *expr_str = sl_string_from_symbol_path(state, proto.expression_path);
      char *type_str = sl_string_from_symbol_path(state, (*param)->type);
      LOG_NORMAL(state->log_out,
        "Cannot add expression '%s' because there is no such type '%s'.\n",
        expr_str, type_str);
      free(expr_str);
      free(type_str);
      free_expression(e);
      free(e);
      return sl_LogicError_SymbolAlreadyExists;
    }
    p.name_id = logic_state_add_string(state, (*param)->name);
    p.type_id = type_id;
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

  /* Check to see if the expression is defined in terms of something else. */
  e->replace_with = NULL;
  if (proto.replace_with != NULL)
    e->replace_with = copy_value(proto.replace_with);

  sl_LogicSymbol sym;
  sym.path = sl_copy_symbol_path(proto.expression_path);
  sym.type = sl_LogicSymbolType_Expression;
  sym.object = e;

  e->path = sym.path;

  add_symbol(state, sym);

  char *expr_str = sl_string_from_symbol_path(state, proto.expression_path);
  LOG_NORMAL(state->log_out,
    "Successfully added expression '%s'.\n", expr_str);
  free(expr_str);
  if (verbose)
  {
    expr_str = string_from_expression(state, e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);

    for (size_t i = 0; i < ARR_LENGTH(e->bindings); ++i)
    {
      Value *binding = *ARR_GET(e->bindings, i);
      char *binding_str = string_from_value(state, binding);
      LOG_VERBOSE(state->log_out, "Binds: '%s'.\n", binding_str);
      free(binding_str);
    }
  }

  return sl_LogicError_None;
}

/* Values */
Value * sl_logic_make_dummy_value(sl_LogicState *state,
    uint32_t id, const sl_SymbolPath *type_path)
{
  Value *value;
  uint32_t type_id;
  const sl_LogicSymbol *type_sym;
  const struct Type *type;
  sl_LogicError err;
  value = SL_NEW(Value);
  value->value_type = ValueTypeDummy;
  value->parent = NULL;
  err = sl_logic_get_symbol_id(state, type_path, &type_id);
  if (err != sl_LogicError_None) {
    char *type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out,
        "Cannot create dummy value because there is no such type '%s'.\n",
        type_str);
    free(type_str);
    free(value);
    return NULL;
  }
  type_sym = sl_logic_get_symbol_by_id(state, type_id);
  if (type_sym->type != sl_LogicSymbolType_Type) {
    char *type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out,
        "Cannot create dummy value because '%s' is not a type.\n",
        type_str);
    free(type_str);
    free(value);
    return NULL;
  }
  type = (struct Type *)type_sym->object;
  if (!type->dummies) {
    char *type_str = sl_string_from_symbol_path(state, type_path);
    LOG_NORMAL(state->log_out,
        "Cannot create dummy value because type '%s' does not support dummies.\n",
        type_str);
    free(type_str);
    free(value);
    return NULL;
  }
  value->type_id = type_id;
  value->content.dummy_id = id;
  return value;
}

Value *
new_variable_value(sl_LogicState *state, const char *name,
    const sl_SymbolPath *type)
{
  Value *value = malloc(sizeof(Value));
  uint32_t type_id;
  sl_LogicError err;
  value->content.variable_name_id = logic_state_add_string(state, name);
  value->value_type = ValueTypeVariable;
  value->parent = NULL;
  err = sl_logic_get_symbol_id(state, type, &type_id);
  if (err != sl_LogicError_None)
  {
    char *type_str = sl_string_from_symbol_path(state, type);
    LOG_NORMAL(state->log_out,
      "Cannot create value because there is no such type '%s'.\n", type_str);
    free(type_str);
    free(value);
    return NULL;
  }
  value->type_id = type_id;
  return value;
}

Value *
new_constant_value(sl_LogicState *state, const sl_SymbolPath *constant)
{
  Value *value;
  value = SL_NEW(Value);
  value->value_type = ValueTypeConstant;
  value->parent = NULL;
  value->content.constant.constant_latex = NULL;

  /* Is this a member of a constspace or a is it an individually declared
     constant? */
  if (sl_get_symbol_path_length(constant) >= 2)
  {
    sl_SymbolPath *container_path;
    const sl_LogicSymbol *constspace;
    container_path = sl_copy_symbol_path(constant);
    sl_pop_symbol_path(container_path);
    constspace = locate_symbol_with_type(state, container_path,
      sl_LogicSymbolType_Constspace);
    sl_free_symbol_path(container_path);
    if (constspace != NULL)
    {
      const struct Constspace *constspace_obj;
      constspace_obj = (struct Constspace *)constspace->object;
      value->type_id = constspace_obj->type_id;
      value->content.constant.constant_path = sl_copy_symbol_path(constant);
      return value;
    }
  }
  sl_LogicSymbol *constant_symbol = locate_symbol_with_type(state,
    constant, sl_LogicSymbolType_Constant);
  if (constant_symbol == NULL)
  {
    char *const_str = sl_string_from_symbol_path(state, constant);
    LOG_NORMAL(state->log_out,
      "Cannot create value because there is no such constant '%s'.\n", const_str);
    free(const_str);
    free(value);
    return NULL;
  }
  const struct Constant *constant_obj =
    (struct Constant *)constant_symbol->object;
  value->content.constant.constant_path =
      sl_copy_symbol_path(constant_obj->path);
  value->type_id = constant_obj->type_id;
  value->content.constant.constant_latex = strdup(constant_obj->latex_format);

  return value;
}

Value *
new_composition_value(sl_LogicState *state, const sl_SymbolPath *expr_path,
  Value * const *args)
{
  Value *value = malloc(sizeof(Value));
  uint32_t expr_id;
  sl_LogicError err;
  value->value_type = ValueTypeComposition;
  value->parent = NULL;
  err = sl_logic_get_symbol_id(state, expr_path, &expr_id);
  if (err != sl_LogicError_None)
  {
    char *expr_str = sl_string_from_symbol_path(state, expr_path);
    LOG_NORMAL(state->log_out,
      "Cannot create value because there is no such expression '%s'.\n",
      expr_str);
    free(expr_str);
    free(value);
    return NULL;
  }
  value->content.composition.expression_id = expr_id;
  {
    const sl_LogicSymbol *expr_sym = sl_logic_get_symbol_by_id(state,
        expr_id);
    const struct Expression *expr = (struct Expression *)expr_sym->object;
    value->type_id = expr->type_id;
  }

  ARR_INIT(value->content.composition.arguments);
  for (Value * const *arg = args;
    *arg != NULL; ++arg)
  {
    Value *arg_copy = copy_value(*arg);
    arg_copy->parent = value;
    ARR_APPEND(value->content.composition.arguments, arg_copy);
  }

  /* Make sure that the arguments match the types of the parameters of
     the expression. */
  {
    const sl_LogicSymbol *expr_sym = sl_logic_get_symbol_by_id(state,
        expr_id);
    const struct Expression *expr = (struct Expression *)expr_sym->object;
    if (ARR_LENGTH(value->content.composition.arguments)
        != ARR_LENGTH(expr->parameters)) {
      char *expr_str = sl_string_from_symbol_path(state, expr_path);
      LOG_NORMAL(state->log_out,
        "Cannot create value because the wrong number of arguments are supplied to the expression '%s'\n",
        expr_str);
      free(expr_str);
      free_value(value);
      return NULL;
    }
    ArgumentArray args_array;
    ARR_INIT(args_array);
    for (size_t i = 0; i < ARR_LENGTH(value->content.composition.arguments);
        ++i) {
      Value *arg = *ARR_GET(value->content.composition.arguments, i);
      const struct Parameter *param = ARR_GET(expr->parameters, i);
      struct Argument argument;
      argument.name_id = param->name_id;
      argument.value = copy_value(arg);
      ARR_APPEND(args_array, argument);
      if (arg->type_id != param->type_id)
      {
        char *expr_str = sl_string_from_symbol_path(state, expr_path);
        LOG_NORMAL(state->log_out,
          "Cannot create value because the type of an argument does not match the required value of the corresponding parameter of expression '%s'\n",
          expr_str);
        free(expr_str);
        free_value(value);
        return NULL;
      }
    }
    for (size_t i = 0; i < ARR_LENGTH(args_array); ++i) {
      struct Argument *arg = ARR_GET(args_array, i);
      free_value(arg->value);
    }
    ARR_FREE(args_array);
  }

  return value;
}

sl_LogicError
add_axiom(sl_LogicState *state, struct PrototypeTheorem proto)
{
  if (locate_symbol(state, proto.theorem_path) != NULL)
  {
    char *axiom_str = sl_string_from_symbol_path(state, proto.theorem_path);
    LOG_NORMAL(state->log_out,
      "Cannot add axiom '%s' because the path is in use.\n", axiom_str);
    free(axiom_str);
    return sl_LogicError_SymbolAlreadyExists;
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
    uint32_t type_id;
    sl_LogicError err;
    err = sl_logic_get_symbol_id(state, (*param)->type, &type_id);
    if (err != sl_LogicError_None)
    {
      char *axiom_str = sl_string_from_symbol_path(state, proto.theorem_path);
      char *type_str = sl_string_from_symbol_path(state, (*param)->type);
      LOG_NORMAL(state->log_out,
        "Cannot add axiom '%s' because there is no such type '%s'.\n",
        axiom_str, type_str);
      free(axiom_str);
      free(type_str);
      //free_expression(e);
      free(a);
      return sl_LogicError_SymbolAlreadyExists;
    }
    p.name_id = logic_state_add_string(state, (*param)->name);
    p.type_id = type_id;
    ARR_APPEND(a->parameters, p);
  }

  /* Requirements. */
  ARR_INIT(a->requirements);
  for (struct PrototypeRequirement **req = proto.requirements;
    *req != NULL; ++req)
  {
    struct Requirement requirement;
    int err = make_requirement(state, &requirement, *req);

    if (err == 0)
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

  sl_LogicSymbol sym;
  sym.path = sl_copy_symbol_path(proto.theorem_path);
  sym.type = sl_LogicSymbolType_Theorem;
  sym.object = a;

  a->path = sym.path;

  add_symbol(state, sym);

  char *axiom_str = sl_string_from_symbol_path(state, proto.theorem_path);
  LOG_NORMAL(state->log_out,
    "Successfully added axiom '%s'.\n", axiom_str);
  free(axiom_str);

  if (verbose)
  {
    for (size_t i = 0; i < ARR_LENGTH(a->assumptions); ++i)
    {
      char *str = string_from_value(state, *ARR_GET(a->assumptions, i));
      printf("Assumption %zu: %s\n", i, str);
      free(str);
    }
    for (size_t i = 0; i < ARR_LENGTH(a->inferences); ++i)
    {
      char *str = string_from_value(state, *ARR_GET(a->inferences, i));
      printf("Inference %zu: %s\n", i, str);
      free(str);
    }
    /*expr_str = string_from_expression(e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);*/
  }

  return sl_LogicError_None;
}

struct ProofEnvironment *
new_proof_environment()
{
  struct ProofEnvironment *env = SL_NEW(struct ProofEnvironment);
  if (env == NULL)
    return NULL;
  ARR_INIT(env->parameters); /* TODO: check these. */
  ARR_INIT(env->requirements);
  ARR_INIT(env->proven);
  return env;
}

void
free_proof_environment(struct ProofEnvironment *env)
{
  ARR_FREE(env->parameters);
  ARR_FREE(env->requirements);
  for (size_t i = 0; i < ARR_LENGTH(env->proven); ++i)
    free_value(*ARR_GET(env->proven, i));
  ARR_FREE(env->proven);
  SL_FREE(env);
}

static bool
statement_proven(const Value *statement, const struct ProofEnvironment *env)
{
  for (size_t i = 0; i < ARR_LENGTH(env->proven); ++i)
  {
    const Value *s = *ARR_GET(env->proven, i);
    if (values_equal(statement, s))
      return TRUE;
  }
  return FALSE;
}

static int
instantiate_theorem_in_env(struct sl_LogicState *state, const struct Theorem *src,
  ArgumentArray args, struct ProofEnvironment *env, bool force)
{
  /* Check the requirements. */
  if (!force)
  {
    for (size_t i = 0; i < ARR_LENGTH(src->requirements); ++i)
    {
      const struct Requirement *req = ARR_GET(src->requirements, i);
      bool satisfied = evaluate_requirement(state, req, args, env);
      if (!satisfied)
        return 1;
    }

    /* First, instantiate the assumptions. */
    ARR(Value *) instantiated_assumptions;
    ARR_INIT(instantiated_assumptions);
    for (size_t i = 0; i < ARR_LENGTH(src->assumptions); ++i)
    {
      const Value *assumption = *ARR_GET(src->assumptions, i);
      Value *instantiated_0 = instantiate_value(assumption, args);
      Value *instantiated = reduce_expressions(state, instantiated_0);
      free_value(instantiated_0);
      if (instantiated == NULL)
        return 1;
      ARR_APPEND(instantiated_assumptions, instantiated);
    }

    /* Verify that each assumption has been proven. */
    for (size_t i = 0; i < ARR_LENGTH(instantiated_assumptions); ++i)
    {
      Value *assumption = *ARR_GET(instantiated_assumptions, i);
      if (!statement_proven(assumption, env))
      {
        char *theorem_str = sl_string_from_symbol_path(state, src->path);
        char *assumption_str = string_from_value(state, assumption);
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
    Value *instantiated_0 = instantiate_value(inference, args);
    Value *instantiated = reduce_expressions(state, instantiated_0);
    free_value(instantiated_0);
    if (instantiated == NULL)
      return 1;
    ARR_APPEND(env->proven, instantiated);
  }

  return 0;
}

static void
list_proven(sl_LogicState *state, const struct ProofEnvironment *env)
{
  LOG_NORMAL(state->log_out, "Statements proven:\n");
  for (size_t i = 0; i < ARR_LENGTH(env->proven); ++i)
  {
    Value *stmt = *ARR_GET(env->proven, i);
    char *str = string_from_value(state, stmt);
    LOG_NORMAL(state->log_out, "> '%s'\n", str);
    free(str);
  }
}

/* TODO: The return value should be a struct, or modify the PrototypeTheorem,
   in order to propagate errors with full detail. */
sl_LogicError
add_theorem(sl_LogicState *state, struct PrototypeTheorem proto)
{
  if (locate_symbol(state, proto.theorem_path) != NULL)
  {
    char *axiom_str = sl_string_from_symbol_path(state, proto.theorem_path);
    LOG_NORMAL(state->log_out,
      "Cannot add theorem '%s' because the path is in use.\n", axiom_str);
    free(axiom_str);
    return sl_LogicError_SymbolAlreadyExists;
  }

  struct Theorem *a = malloc(sizeof(struct Theorem));
  a->is_axiom = FALSE;
  a->id = state->next_id;
  ++state->next_id;

  /* Environment setup. */
  struct ProofEnvironment *env = new_proof_environment();

  /* Parameters. */
  ARR_INIT(a->parameters);
  for (struct PrototypeParameter **param = proto.parameters;
    *param != NULL; ++param)
  {
    struct Parameter p;
    uint32_t type_id;
    sl_LogicError err;
    err = sl_logic_get_symbol_id(state, (*param)->type, &type_id);
    if (err != sl_LogicError_None)
    {
      char *axiom_str = sl_string_from_symbol_path(state, proto.theorem_path);
      char *type_str = sl_string_from_symbol_path(state, (*param)->type);
      LOG_NORMAL(state->log_out,
        "Cannot add theorem '%s' because there is no such type '%s'.\n",
        axiom_str, type_str);
      free(axiom_str);
      free(type_str);
      //free_expression(e);
      free(a);
      return sl_LogicError_SymbolAlreadyExists;
    }
    p.name_id = logic_state_add_string(state, (*param)->name);
    p.type_id = type_id;
    ARR_APPEND(a->parameters, p);
    ARR_APPEND(env->parameters, p);
  }

  /* Requirements. */
  ARR_INIT(a->requirements);
  for (struct PrototypeRequirement **req = proto.requirements;
    *req != NULL; ++req)
  {
    struct Requirement requirement;
    int err = make_requirement(state, &requirement, *req);

    if (err == 0)
    {
      ARR_APPEND(a->requirements, requirement);
      ARR_APPEND(env->requirements, requirement);
    }
  }

  /* Assumptions & inferences. */
  ARR_INIT(a->assumptions);
  ARR_INIT(a->inferences);
  for (Value **assume = proto.assumptions;
    *assume != NULL; ++assume)
  {
    ARR_APPEND(a->assumptions, copy_value(*assume));
    Value *reduced = reduce_expressions(state, *assume);
    ARR_APPEND(env->proven, reduced);
  }
  for (Value **infer = proto.inferences;
    *infer != NULL; ++infer)
  {
    ARR_APPEND(a->inferences, copy_value(*infer));
  }

  /* Finally, check the proof. */
  ARR_INIT(a->steps);
  for (struct PrototypeProofStep **step = proto.steps;
    *step != NULL; ++step)
  {
    struct TheoremReference ref;
    ARR_INIT(ref.arguments);
    const sl_LogicSymbol *thm_symbol = locate_symbol_with_type(state,
      (*step)->theorem_path, sl_LogicSymbolType_Theorem);
    if (thm_symbol == NULL)
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced in proof does not exist.\n");
      return sl_LogicError_SymbolAlreadyExists;
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
      return sl_LogicError_SymbolAlreadyExists;
    }

    ArgumentArray args;
    ARR_INIT(args);
    for (size_t i = 0; i < args_n; ++i)
    {
      struct Parameter *param = ARR_GET(ref.theorem->parameters, i);

      struct Argument arg;
      arg.name_id = param->name_id;
      arg.value = copy_value((*step)->arguments[i]);

      ARR_APPEND(ref.arguments, copy_value(arg.value));

      if (arg.value->type_id != param->type_id)
      {
        LOG_NORMAL(state->log_out,
          "Cannot add theorem because an axiom/theorem referenced received an argument with the wrong type.\n");
        return sl_LogicError_SymbolAlreadyExists;
      }

      ARR_APPEND(args, arg);
    }

    if (instantiate_theorem_in_env(state, ref.theorem, args, env, FALSE) != 0)
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an axiom/theorem referenced could not be instantiated.\n");
      list_proven(state, env);
      return sl_LogicError_SymbolAlreadyExists;
    }

    for (size_t i = 0; i < args_n; ++i)
    {
      struct Argument *arg = ARR_GET(args, i);
      free_value(arg->value);
    }
    ARR_FREE(args);
    ARR_APPEND(a->steps, ref);
  }

  /* Check that all the inferences have been proven. */
  for (size_t i = 0; i < ARR_LENGTH(a->inferences); ++i)
  {
    Value *infer = *ARR_GET(a->inferences, i);
    Value *reduced = reduce_expressions(state, infer);
    if (!statement_proven(reduced, env))
    {
      LOG_NORMAL(state->log_out,
        "Cannot add theorem because an inference was not proven.\n");
      free_value(reduced);
      return sl_LogicError_SymbolAlreadyExists;
    }
    free_value(reduced);
  }

  /* Free all the statements that we've proven. */
  sl_LogicSymbol sym;
  sym.path = sl_copy_symbol_path(proto.theorem_path);
  sym.type = sl_LogicSymbolType_Theorem;
  sym.object = a;

  a->path = sym.path;

  add_symbol(state, sym);

  char *axiom_str = sl_string_from_symbol_path(state, proto.theorem_path);
  LOG_NORMAL(state->log_out,
    "Successfully added theorem '%s'.\n", axiom_str);
  free(axiom_str);

  if (verbose)
  {
    for (size_t i = 0; i < ARR_LENGTH(a->assumptions); ++i)
    {
      char *str = string_from_value(state, *ARR_GET(a->assumptions, i));
      printf("Assumption %zu: %s\n", i, str);
      free(str);
    }
    for (size_t i = 0; i < ARR_LENGTH(a->inferences); ++i)
    {
      char *str = string_from_value(state, *ARR_GET(a->inferences, i));
      printf("Inference %zu: %s\n", i, str);
      free(str);
    }
    /*expr_str = string_from_expression(e);
    LOG_VERBOSE(state->log_out, "Signature: '%s'.\n", expr_str);
    free(expr_str);*/
  }

  free_proof_environment(env);
  return sl_LogicError_None;
}
