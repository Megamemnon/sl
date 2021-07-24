#include "core.h"
#include <string.h>

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
    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      Value *arg = *ARR_GET(context->arguments, i);
        make_substitution_in_place(source, target, arg);
    }
  }
}

static bool
new_bindings_exist(LogicState *state, const Value *context)
{
  if (context->value_type == ValueTypeComposition)
  {
    ArgumentArray args_array;
    ARR_INIT(args_array);
    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      Value *arg = *ARR_GET(context->arguments, i);
      bool child_binds = new_bindings_exist(state, arg);
      if (child_binds)
        return TRUE;

      const struct Parameter *param =
        ARR_GET(context->expression->parameters, i);
      struct Argument argument;
      argument.name = strdup(param->name);
      argument.value = copy_value(arg);
      ARR_APPEND(args_array, argument);
    }

    /* Look for things to bind. */
    for (size_t i = 0; i < ARR_LENGTH(context->expression->bindings); ++i)
    {
      const Value *binding = *ARR_GET(context->expression->bindings, i);
      Value *instantiated = instantiate_value(state, binding, args_array);

      ValueArray occurrences;
      ARR_INIT(occurrences);
      enumerate_value_occurrences(instantiated, context, &occurrences);
      for (size_t j = 0; j < ARR_LENGTH(occurrences); ++j)
      {
        Value *occurrence = *ARR_GET(occurrences, j);
        if (occurrence->bound == FALSE)
          return TRUE;
      }
      ARR_FREE(occurrences);

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

bool
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

bool
evaluate_not_free(struct LogicState *state,
  const Value *target, const Value *context)
{
  /* TODO: Instead of requiring everything to be terminal, in cases that
     we have non-terminals, figure out what must be required in order to
     make it work and check for that requirement in the environment. */
  if (!value_terminal(target) || !value_terminal(context))
    return FALSE;

  bool not_free = TRUE;
  ValueArray occurrences;
  ARR_INIT(occurrences);
  enumerate_value_occurrences(target, context, &occurrences);
  for (size_t i = 0; i < ARR_LENGTH(occurrences); ++i)
  {
    const Value *occurrence = *ARR_GET(occurrences, i);
    if (!occurrence->bound)
      not_free = FALSE;
  }
  ARR_FREE(occurrences);

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
    if (ARR_LENGTH(context->arguments) !=
      ARR_LENGTH(new_context->arguments))
      return FALSE;
    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      const Value *ctx_arg = *ARR_GET(context->arguments, i);
      const Value *new_ctx_arg = *ARR_GET(new_context->arguments, i);
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

bool
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
    if (ARR_LENGTH(context->arguments) != ARR_LENGTH(new_context->arguments))
      return FALSE;
    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      const Value *ctx_arg = *ARR_GET(context->arguments, i);
      const Value *new_ctx_arg = *ARR_GET(new_context->arguments, i);
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

bool
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
