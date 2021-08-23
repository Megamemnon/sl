#include "core.h"
#include <string.h>

void
free_value(Value *value)
{
  if (value->value_type == ValueTypeDummy) {

  } if (value->value_type == ValueTypeVariable) {

  }
  else if (value->value_type == ValueTypeConstant)
  {
    sl_free_symbol_path(value->content.constant.constant_path);
    if (value->content.constant.constant_latex != NULL)
      free(value->content.constant.constant_latex);
  }
  else if (value->value_type == ValueTypeComposition)
  {
    for (size_t i = 0; i < ARR_LENGTH(value->content.composition.arguments);
        ++i) {
      Value *arg = *ARR_GET(value->content.composition.arguments, i);
      free_value(arg);
    }
    ARR_FREE(value->content.composition.arguments);
  }
  free(value);
}

void
copy_value_to(Value *dst, const Value *src)
{
  dst->value_type = src->value_type;
  dst->type_id = src->type_id;
  if (src->value_type == ValueTypeDummy) {
    dst->content.dummy_id = src->content.dummy_id;
  } if (src->value_type == ValueTypeVariable) {
    dst->content.variable_name_id = src->content.variable_name_id;
  }
  else if (src->value_type == ValueTypeConstant)
  {
    dst->content.constant.constant_path =
        sl_copy_symbol_path(src->content.constant.constant_path);
    if (src->content.constant.constant_latex != NULL)
      dst->content.constant.constant_latex =
          strdup(src->content.constant.constant_latex);
    else
      dst->content.constant.constant_latex = NULL;
  }
  else if (src->value_type == ValueTypeComposition)
  {
    dst->content.composition.expression_id =
        src->content.composition.expression_id;
    ARR_INIT(dst->content.composition.arguments);
    for (size_t i = 0; i < ARR_LENGTH(src->content.composition.arguments);
        ++i) {
      const struct Value *arg =
          *ARR_GET(src->content.composition.arguments, i);
      struct Value *arg_copy = copy_value(arg);
      arg_copy->parent = dst;
      ARR_APPEND(dst->content.composition.arguments, arg_copy);
    }
  }
}

Value *
copy_value(const Value *value)
{
  Value *v = SL_NEW(Value);
  v->parent = NULL;
  copy_value_to(v, value);
  return v;
}

bool
values_equal(const Value *a, const Value *b)
{
  if (a->value_type != b->value_type)
    return FALSE;
  switch (a->value_type)
  {
    case ValueTypeDummy:
      if (a->content.dummy_id != b->content.dummy_id)
        return FALSE;
      break;
    case ValueTypeConstant:
      if (!sl_symbol_paths_equal(a->content.constant.constant_path,
          b->content.constant.constant_path))
        return FALSE;
      break;
    case ValueTypeVariable:
      if (a->type_id != b->type_id)
        return FALSE;
      if (a->content.variable_name_id != b->content.variable_name_id)
        return FALSE;
      break;
    case ValueTypeComposition:
      if (a->type_id != b->type_id)
        return FALSE;
      if (a->content.composition.expression_id
          != b->content.composition.expression_id)
        return FALSE;
      if (ARR_LENGTH(a->content.composition.arguments)
          != ARR_LENGTH(b->content.composition.arguments))
        return FALSE;
      for (size_t i = 0; i < ARR_LENGTH(a->content.composition.arguments);
        ++i) {
        const Value *arg_a = *ARR_GET(a->content.composition.arguments, i);
        const Value *arg_b = *ARR_GET(b->content.composition.arguments, i);
        if (!values_equal(arg_a, arg_b))
          return FALSE;
      }
      break;
  }
  return TRUE;
}

bool value_terminal(const sl_LogicState *state, const Value *v)
{
  switch (v->value_type)
  {
    case ValueTypeDummy:
      {
        const sl_LogicSymbol *type_sym = sl_logic_get_symbol_by_id(state,
            v->type_id);
        const struct Type *type = (struct Type *)type_sym->object;
        return type->atomic;
      }
      break;
    case ValueTypeConstant:
      return TRUE;
      break;
    case ValueTypeVariable:
      {
        const sl_LogicSymbol *type_sym = sl_logic_get_symbol_by_id(state,
            v->type_id);
        const struct Type *type = (struct Type *)type_sym->object;
        return type->atomic;
      }
      break;
    case ValueTypeComposition:
      for (size_t i = 0; i < ARR_LENGTH(v->content.composition.arguments);
        ++i) {
        Value *arg = *ARR_GET(v->content.composition.arguments, i);
        if (!value_terminal(state, arg))
          return FALSE;
      }
      return TRUE;
      break;
  }
}

char *
string_from_value(const sl_LogicState *state, const Value *value)
{
  switch (value->value_type)
  {
    case ValueTypeDummy:
      {
        char *dummy_str;
        asprintf(&dummy_str, "Dummy #%u", value->content.dummy_id);
        return dummy_str;
      }
      break;
    case ValueTypeComposition:
      {
        const sl_LogicSymbol *expr_sym = sl_logic_get_symbol_by_id(state,
            value->content.composition.expression_id);
        const struct Expression *expr = (struct Expression *)expr_sym->object;
        char *expr_str = sl_string_from_symbol_path(state, expr->path);
        char *str;
        if (ARR_LENGTH(value->content.composition.arguments) == 0)
        {
          size_t len = 3 + strlen(expr_str);
          str = malloc(len);
          char *c = str;
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
          char **args = malloc(sizeof(char *)
              * ARR_LENGTH(value->content.composition.arguments));
          for (size_t i = 0;
              i < ARR_LENGTH(value->content.composition.arguments); ++i) {
            const struct Value *arg =
                *ARR_GET(value->content.composition.arguments, i);
            args[i] = string_from_value(state, arg);
            len += strlen(args[i]);
          }
          len += (ARR_LENGTH(value->content.composition.arguments) - 1) * 2;

          str = malloc(len);
          char *c = str;
          strcpy(c, expr_str);
          c += strlen(expr_str);
          *c = '(';
          ++c;
          bool first_arg = TRUE;
          for (size_t i = 0;
              i < ARR_LENGTH(value->content.composition.arguments); ++i) {
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
        char *const_str = sl_string_from_symbol_path(state,
            value->content.constant.constant_path);
        size_t len = 1 + strlen(const_str);
        char *str = malloc(len);
        char *c = str;
        strcpy(c, const_str);
        c += strlen(const_str);
        *c = '\0';
        free(const_str);
        return str;
      }
      break;
    case ValueTypeVariable:
      {
        size_t len = 2 + strlen(logic_state_get_string(state,
            value->content.variable_name_id));
        char *str = malloc(len);
        char *c = str;
        *c = '$';
        ++c;
        strcpy(c, logic_state_get_string(state,
            value->content.variable_name_id));
        c += strlen(logic_state_get_string(state,
            value->content.variable_name_id));
        *c = '\0';
        return str;
      }
      break;
  }
}

void
enumerate_value_occurrences(const Value *target, const Value *search_in,
  ValueArray *occurrences)
{
  if (values_equal(target, search_in))
  {
    ARR_APPEND(*occurrences, search_in);
  }
  else if (search_in->value_type == ValueTypeComposition)
  {
    for (size_t i = 0;
        i < ARR_LENGTH(search_in->content.composition.arguments); ++i) {
      const Value *arg = *ARR_GET(search_in->content.composition.arguments, i);
      enumerate_value_occurrences(target, arg, occurrences);
    }
  }
}

unsigned int
count_value_occurrences(const Value *target, const Value *search_in)
{
  if (values_equal(target, search_in)) {
    return 1;
  } else if (search_in->value_type == ValueTypeComposition) {
    unsigned int child_occurrences = 0;
    for (size_t i = 0;
        i < ARR_LENGTH(search_in->content.composition.arguments); ++i) {
      const Value *arg = *ARR_GET(search_in->content.composition.arguments, i);
      child_occurrences += count_value_occurrences(target, arg);
    }
    return child_occurrences;
  } else {
    return 0;
  }
}

static bool value_is_irreducible(const sl_LogicState *state,
    const Value *value)
{
  switch (value->value_type)
  {
    case ValueTypeDummy:
      return TRUE;
      break;
    case ValueTypeConstant:
      return TRUE;
      break;
    case ValueTypeVariable:
      return TRUE;
      break;
    case ValueTypeComposition:
      {
        const sl_LogicSymbol *expr_sym = sl_logic_get_symbol_by_id(state,
            value->content.composition.expression_id);
        const struct Expression *expr = (struct Expression *)expr_sym->object;
        if (expr->replace_with != NULL)
          return FALSE;
        for (size_t i = 0;
            i < ARR_LENGTH(value->content.composition.arguments); ++i) {
          const Value *arg = *ARR_GET(value->content.composition.arguments, i);
          if (!value_is_irreducible(state, arg))
            return FALSE;
        }
        return TRUE;
      }
      break;
  }
}

static Value * do_reduction_step(const sl_LogicState *state,
    const Value *value)
{
  switch (value->value_type)
  {
    case ValueTypeDummy:
      return copy_value(value);
      break;
    case ValueTypeConstant:
      return copy_value(value);
      break;
    case ValueTypeVariable:
      return copy_value(value);
      break;
    case ValueTypeComposition:
      /* TODO: check that types and number of arguments match. Probably best
         to do this here as well as in the expression creation function. */
      {
        const sl_LogicSymbol *expr_sym = sl_logic_get_symbol_by_id(state,
            value->content.composition.expression_id);
        const struct Expression *expr = (struct Expression *)expr_sym->object;
        if (expr->replace_with == NULL)
        {
          Value *new = SL_NEW(Value);
          new->value_type = ValueTypeComposition;
          new->parent = NULL;
          new->content.composition.expression_id =
              value->content.composition.expression_id;
          new->type_id = value->type_id;
          ARR_INIT(new->content.composition.arguments);
          for (size_t i = 0;
              i < ARR_LENGTH(value->content.composition.arguments); ++i)
          {
            const Value *arg =
                *ARR_GET(value->content.composition.arguments, i);
            Value *reduced = do_reduction_step(state, arg);
            reduced->parent = new;
            ARR_APPEND(new->content.composition.arguments, reduced);
          }
          return new;
        }
        else
        {
          Value *new;
          if (expr->replace_with->value_type == ValueTypeComposition) {
            ArgumentArray args;
            ARR_INIT(args);
            for (size_t i = 0;
                i < ARR_LENGTH(value->content.composition.arguments); ++i) {
              struct Argument arg;
              const struct Parameter *param;
              param = ARR_GET(expr->parameters, i);
              arg.name_id = param->name_id;
              arg.value = do_reduction_step(state,
                  *ARR_GET(value->content.composition.arguments, i));
              ARR_APPEND(args, arg);
            }
            new = instantiate_value(expr->replace_with, args);
            for (size_t i = 0; i < ARR_LENGTH(args); ++i) {
              struct Argument *arg = ARR_GET(args, i);
              free_value(arg->value);
            }
            ARR_FREE(args);
            return new;
          }
          else
          {
            return copy_value(expr->replace_with);
          }
        }
      }
      break;
  }
}

Value * reduce_expressions(const sl_LogicState *state, const Value *value)
{
  Value *reduced = copy_value(value);
  while (!value_is_irreducible(state, reduced))
  {
    Value *tmp = do_reduction_step(state, reduced);
    free_value(reduced);
    reduced = tmp;
  }
  return reduced;
}

Value *
instantiate_value(const Value *src, ArgumentArray args)
{
  switch (src->value_type)
  {
    case ValueTypeDummy:
      return copy_value(src);
      break;
    case ValueTypeConstant:
      return copy_value(src);
      break;
    case ValueTypeVariable:
      /* Find the corresponding argument. */
      {
        const struct Argument *arg = NULL;
        for (size_t i = 0; i < ARR_LENGTH(args); ++i)
        {
          const struct Argument *a = ARR_GET(args, i);
          if (a->name_id == src->content.variable_name_id) {
            arg = a;
            break;
          }
        }
        if (arg == NULL) {
          return NULL;
        }
        if (arg->value->type_id != src->type_id) {
          return NULL;
        }
        return copy_value(arg->value);
      }
      break;
    case ValueTypeComposition:
      {
        Value *dst = SL_NEW(Value);
        dst->type_id = src->type_id;
        dst->value_type = ValueTypeComposition;
        dst->content.composition.expression_id =
            src->content.composition.expression_id;
        dst->parent = NULL;
        ARR_INIT(dst->content.composition.arguments);
        for (size_t i = 0;
            i < ARR_LENGTH(src->content.composition.arguments); ++i) {
          const Value *arg = *ARR_GET(src->content.composition.arguments, i);
          Value *instantiated_arg = instantiate_value(arg, args);
          instantiated_arg->parent = dst;
          ARR_APPEND(dst->content.composition.arguments, instantiated_arg);
        }
        return dst;
      }
      break;
  }
  return 0;
}
