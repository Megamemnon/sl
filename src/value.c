#include "core.h"
#include <string.h>

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
    for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
    {
      Value *arg = *ARR_GET(value->arguments, i);
      free_value(arg);
    }
    ARR_FREE(value->arguments);
  }
  free(value);
}

void
copy_value_to(Value *dst, const Value *src)
{
  dst->value_type = src->value_type;
  dst->type = src->type;
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
    ARR_INIT(dst->arguments);
    for (size_t i = 0; i < ARR_LENGTH(src->arguments); ++i)
    {
      const struct Value *arg = *ARR_GET(src->arguments, i);
      struct Value *arg_copy = copy_value(arg);
      arg_copy->parent = dst;
      ARR_APPEND(dst->arguments, arg_copy);
    }
  }
}

Value *
copy_value(const Value *value)
{
  Value *v = malloc(sizeof(Value));
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
      if (ARR_LENGTH(a->arguments) != ARR_LENGTH(b->arguments))
        return FALSE;
      for (size_t i = 0; i < ARR_LENGTH(a->arguments); ++i)
      {
        const Value *arg_a = *ARR_GET(a->arguments, i);
        const Value *arg_b = *ARR_GET(b->arguments, i);
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
      for (size_t i = 0; i < ARR_LENGTH(v->arguments); ++i)
      {
        Value *arg = *ARR_GET(v->arguments, i);
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
        if (ARR_LENGTH(value->arguments) == 0)
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
          char **args = malloc(sizeof(char *) * ARR_LENGTH(value->arguments));
          for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
          {
            const struct Value *arg = *ARR_GET(value->arguments, i);
            args[i] = string_from_value(arg);
            len += strlen(args[i]);
          }
          len += (ARR_LENGTH(value->arguments) - 1) * 2;

          str = malloc(len);
          char *c = str;
          strcpy(c, expr_str);
          c += strlen(expr_str);
          *c = '(';
          ++c;
          bool first_arg = TRUE;
          for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
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
        size_t len = 2 + strlen(value->variable_name);
        char *str = malloc(len);
        char *c = str;
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
    for (size_t i = 0; i < ARR_LENGTH(search_in->arguments); ++i)
    {
      const Value *arg = *ARR_GET(search_in->arguments, i);
      enumerate_value_occurrences(target, arg, occurrences);
    }
  }
}

static bool
value_is_irreducible(const Value *value)
{
  switch (value->value_type)
  {
    case ValueTypeConstant:
      return TRUE;
      break;
    case ValueTypeVariable:
      return TRUE;
      break;
    case ValueTypeComposition:
      if (value->expression->replace_with != NULL)
        return FALSE;
      for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
      {
        const Value *arg = *ARR_GET(value->arguments, i);
        if (!value_is_irreducible(arg))
          return FALSE;
      }
      return TRUE;
      break;
  }
}

static Value *
do_reduction_step(const Value *value)
{
  switch (value->value_type)
  {
    case ValueTypeConstant:
      return copy_value(value);
      break;
    case ValueTypeVariable:
      return copy_value(value);
      break;
    case ValueTypeComposition:
      /* TODO: check that types and number of arguments match. Probably best
         to do this here as well as in the expression creation function. */
      if (value->expression->replace_with == NULL)
      {
        Value *new = malloc(sizeof(Value));
        new->value_type = ValueTypeComposition;
        new->parent = NULL;
        new->expression = value->expression;
        new->type = value->type;
        ARR_INIT(new->arguments);
        for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
        {
          const Value *arg = *ARR_GET(value->arguments, i);
          Value *reduced = do_reduction_step(arg);
          char *s1 = string_from_value(arg);
          char *s2 = string_from_value(reduced);
          reduced->parent = new;
          ARR_APPEND(new->arguments, reduced);
        }
        return new;
      }
      else
      {
        Value *new;
        if (value->expression->replace_with->value_type
          == ValueTypeComposition)
        {
          ArgumentArray args;
          ARR_INIT(args);
          for (size_t i = 0; i < ARR_LENGTH(value->arguments); ++i)
          {
            struct Argument arg;
            const struct Parameter *param;
            Value *old_value =
              do_reduction_step(*ARR_GET(value->arguments, i));
            param = ARR_GET(value->expression->parameters, i);
            arg.name = strdup(param->name);
            arg.value = copy_value(old_value);
            ARR_APPEND(args, arg);
          }
          new = instantiate_value(value->expression->replace_with, args);
          ARR_FREE(args);
          return new;
        }
        else
        {
          return copy_value(value->expression->replace_with);
        }
      }
      break;
  }
}

Value *
reduce_expressions(const Value *value)
{
  Value *reduced = copy_value(value);
  while (!value_is_irreducible(reduced))
  {
    Value *tmp = do_reduction_step(reduced);
    free_value(reduced);
    reduced = tmp;
  }
  char *s1 = string_from_value(value);
  char *s2 = string_from_value(reduced);
  return reduced;
}

Value *
instantiate_value(const Value *src, ArgumentArray args)
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
        for (size_t i = 0; i < ARR_LENGTH(args); ++i)
        {
          const struct Argument *a = ARR_GET(args, i);
          if (strcmp(a->name, src->variable_name) == 0)
          {
            arg = a;
            break;
          }
        }
        if (arg == NULL)
        {
          char *value_str = string_from_value(src);
          /*LOG_NORMAL(state->log_out,
            "Cannot instantiate value '%s' because there is no matching argument.\n",
            value_str);*/
          free(value_str);
          return NULL;
        }
        if (!types_equal(arg->value->type, src->type))
        {
          char *value_str = string_from_value(src);
          char *src_type = string_from_symbol_path(src->type->path);
          char *arg_type = string_from_symbol_path(arg->value->type->path);
          /*LOG_NORMAL(state->log_out,
            "Cannot instantiate value '%s' of type '%s' because the variable has type '%s'.\n",
            value_str, src_type, arg_type);*/
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
        dst->parent = NULL;
        ARR_INIT(dst->arguments);
        for (size_t i = 0; i < ARR_LENGTH(src->arguments); ++i)
        {
          const Value *arg = *ARR_GET(src->arguments, i);
          Value *instantiated_arg = instantiate_value(/*state, */arg, args);
          instantiated_arg->parent = dst;
          ARR_APPEND(dst->arguments, instantiated_arg);
        }
        return dst;
      }
      break;
  }
  return 0;
}
