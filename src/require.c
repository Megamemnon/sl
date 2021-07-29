#include "core.h"
#include <string.h>

/* --- Requirement Creation --- */
int
make_requirement(sl_LogicState *state,
  struct Requirement *dst, const struct PrototypeRequirement *src)
{
  ARR_INIT(dst->arguments);
  for (Value **arg = src->arguments; *arg != NULL; ++arg)
    ARR_APPEND(dst->arguments, copy_value(*arg));

  /* Make sure that the number of arguments is correct. */
  if (strcmp(src->require, "distinct") == 0)
  {
    dst->type = RequirementTypeDistinct;
    if (ARR_LENGTH(dst->arguments) < 2)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "free_for") == 0)
  {
    dst->type = RequirementTypeFreeFor;
    if (ARR_LENGTH(dst->arguments) != 3)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "not_free") == 0)
  {
    dst->type = RequirementTypeNotFree;
    if (ARR_LENGTH(dst->arguments) != 2)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "not_bound") == 0)
  {
    dst->type = RequirementTypeNotBound;
    if (ARR_LENGTH(dst->arguments) != 2)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "free") == 0)
  {
    dst->type = RequirementTypeFree;
    if (ARR_LENGTH(dst->arguments) != 2)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "bound") == 0)
  {
    dst->type = RequirementTypeBound;
    if (ARR_LENGTH(dst->arguments) != 2)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "cover_free") == 0)
  {
    dst->type = RequirementTypeCoverFree;
    if (ARR_LENGTH(dst->arguments) < 1)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "cover_bound") == 0)
  {
    dst->type = RequirementTypeCoverBound;
    if (ARR_LENGTH(dst->arguments) < 1)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "substitution") == 0)
  {
    dst->type = RequirementTypeSubstitution;
    if (ARR_LENGTH(dst->arguments) != 4)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else if (strcmp(src->require, "full_substitution") == 0)
  {
    dst->type = RequirementTypeFullSubstitution;
    if (ARR_LENGTH(dst->arguments) != 4)
    {
      for (size_t i = 0; i < ARR_LENGTH(dst->arguments); ++i)
        free_value(*ARR_GET(dst->arguments, i));
      ARR_FREE(dst->arguments);
      return 1;
    }
  }
  else
  {
    return 1;
  }
  return 0;
}

/* Note that not all cases are treated by this code, as many of them are
   nontrivial. However, each evaluation function only returns true when
   the corresponding statement is true. There are cases where a requirement
   turns out to be true but an evaluation function says false, but these do
   not impede the development of our logic. Since there are only false
   negatives, this only limits the scope of theorems that can be proved. */

/* --- Distinctness --- */
static bool
pair_distinct_in_env(sl_LogicState *state, const struct ProofEnvironment *env,
  const Value *a, const Value *b)
{
  for (size_t i = 0; i < ARR_LENGTH(env->requirements); ++i)
  {
    const struct Requirement *req = ARR_GET(env->requirements, i);
    if (req->type == RequirementTypeDistinct)
    {
      /* TODO: look for distinctness resulting from distinct compositions? */
      bool found_a = FALSE;
      bool found_b = FALSE;
      for (size_t j = 0; j < ARR_LENGTH(req->arguments); ++j)
      {
        Value *v = *ARR_GET(req->arguments, j);
        if (values_equal(v, a))
          found_a = TRUE;
        if (values_equal(v, b))
          found_b = TRUE;
        if (found_a && found_b)
          break;
      }
      if (found_a && found_b)
        return TRUE;
    }
  }
  if (a->value_type != b->value_type)
    return TRUE;
  switch (a->value_type)
  {
    case ValueTypeConstant:
      return !values_equal(a, b);
      break;
    case ValueTypeVariable:
      /* If we did not establish the distinctness of these variables through
         another requirements, then it is possible that they are the same. */
      return FALSE;
      break;
    case ValueTypeComposition:
      if (ARR_LENGTH(a->arguments) != ARR_LENGTH(b->arguments))
        return TRUE;
      if (a->expression->id != b->expression->id) /* TODO: abstract this to its own function. */
        return TRUE;
      for (size_t i = 0; i < ARR_LENGTH(a->arguments); ++i)
      {
        Value *arg_a, *arg_b;
        arg_a = *ARR_GET(a->arguments, i);
        arg_b = *ARR_GET(b->arguments, i);
        if (!pair_distinct_in_env(state, env, arg_a, arg_b))
          return FALSE;
      }
      break;
  }
  return TRUE;
}

static bool
evaluate_distinct(sl_LogicState *state, const struct ProofEnvironment *env,
  ValueArray args)
{
  /* Evaluate each pair of arguments once for distinctness. */
  for (size_t i = 0; i < ARR_LENGTH(args); ++i)
  {
    for (size_t j = i + 1; j < ARR_LENGTH(args); ++j)
    {
      const Value *a, *b;
      bool distinct;
      a = *ARR_GET(args, i);
      b = *ARR_GET(args, j);
      {
        char *a_str, *b_str;
        a_str = string_from_value(a);
        b_str = string_from_value(b);
      }
      distinct = pair_distinct_in_env(state, env, a, b);
      if (!distinct)
        return FALSE;
    }
  }
  return TRUE;
}

/* --- Free for --- */
static bool
value_gets_bound(const Value *source, const Value *context)
{
  switch (source->value_type)
  {
    case ValueTypeConstant:
      /* For a constant, look up through the parents of context. If there is
         a binding equal to source, or if there is a variable that gets
         bound, return true. */
      for (const Value *scope = context->parent; scope != NULL;
        scope = scope->parent)
      {
        ArgumentArray args_array;
        ARR_INIT(args_array);
        for (size_t i = 0; i < ARR_LENGTH(scope->arguments); ++i)
        {
          Value *arg = *ARR_GET(scope->arguments, i);
          const struct Parameter *param =
            ARR_GET(scope->expression->parameters, i);
          struct Argument argument;
          argument.name = strdup(param->name);
          argument.value = copy_value(arg);
          ARR_APPEND(args_array, argument);
        }

        for (size_t i = 0; i < ARR_LENGTH(scope->expression->bindings); ++i)
        {
          const Value *binding = *ARR_GET(scope->expression->bindings, i);
          Value *instantiated_binding = instantiate_value(binding, args_array);
          if (instantiated_binding->value_type == ValueTypeVariable
            || values_equal(instantiated_binding, source))
          {
            return TRUE;
            /* TODO: free. */
          }
          free_value(instantiated_binding);
        }
      }
      return FALSE;
      break;
    case ValueTypeVariable:
      /* If we have a variable, just assume there is a
         production that introduces a sub-value that gets bound if context
         is a child of any binding expressions. */
      for (const Value *scope = context->parent; scope != NULL;
        scope = scope->parent)
      {
        if (ARR_LENGTH(scope->expression->bindings) > 0)
          return TRUE;
      }
      return FALSE;
      break;
    case ValueTypeComposition:
      for (size_t i = 0; i < ARR_LENGTH(source->arguments); ++i)
      {
        const Value *arg = *ARR_GET(source->arguments, i);
        if (value_gets_bound(arg, context))
          return TRUE;
      }
      return FALSE;
      break;
  }
}

static bool
free_for_in_env(const struct ProofEnvironment *env,
  const Value *source, const Value *target, const Value *context)
{
  /* Special case: anything is always free for itself. */
  if (values_equal(source, target))
    return TRUE;

  /* Check if there is a corresponding requirement in the environment. */
  for (size_t i = 0; i < ARR_LENGTH(env->requirements); ++i)
  {
    const struct Requirement *req = ARR_GET(env->requirements, i);
    if (req->type == RequirementTypeFreeFor)
    {
      const Value *r_source, *r_target, *r_context;
      r_source = *ARR_GET(req->arguments, 0);
      r_target = *ARR_GET(req->arguments, 1);
      r_context = *ARR_GET(req->arguments, 2);
      if (values_equal(source, r_source) && values_equal(target, r_target)
        && values_equal(context, r_context))
        return TRUE;
    }
  }

  /* If this is the site of the substitution or a variable, check that
     the source is free for the target. */
  /* TODO: is there no sequence of productions that allows a value of type
     target to be contained as a subexpression of context if context is a
     variable? For now, just operate on the assumption that such a
     substitution is possible. */
  if (values_equal(target, context)
    || context->value_type == ValueTypeVariable)
  {
    /* Then, iterate through the source and look for terms that can
       be bound. */
    return !value_gets_bound(source, context);
  }
  else if (context->value_type == ValueTypeConstant)
  {
    /* Since we didn't match above, we're all good. */
    return TRUE;
  }
  else if (context->value_type == ValueTypeComposition)
  {
    /* Check all the children. */
    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      const Value *arg = *ARR_GET(context->arguments, i);
      if (!free_for_in_env(env, source, target, arg))
        return FALSE;
    }
    return TRUE;
  }
  return TRUE;
}

static bool
evaluate_free_for(struct sl_LogicState *state,
  const struct ProofEnvironment *env, ValueArray args)
{
  const Value *source, *target, *context;
  if (ARR_LENGTH(args) != 3)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  source = *ARR_GET(args, 0);
  target = *ARR_GET(args, 1);
  context = *ARR_GET(args, 2);

  return free_for_in_env(env, source, target, context);
}

/* --- Not Free --- */
static bool
not_free_in_env(const struct ProofEnvironment *env, const Value *target,
  const Value *context)
{
  /* Check if there is a corresponding requirement in the environment. */
  for (size_t i = 0; i < ARR_LENGTH(env->requirements); ++i)
  {
    const struct Requirement *req = ARR_GET(env->requirements, i);
    if (req->type == RequirementTypeNotFree)
    {
      const Value *r_target, *r_context;
      r_target = *ARR_GET(req->arguments, 0);
      r_context = *ARR_GET(req->arguments, 1);
      if (values_equal(target, r_target) && values_equal(context, r_context))
        return TRUE;
    }
  }

  if (values_equal(target, context))
  {
    /* The value occurs free as itself. */
    return FALSE;
  }
  else if (context->value_type == ValueTypeComposition)
  {
    /* For a composition, look at what the expression binds. If the
       context binds the target, then the target cannot be free. If the
       expression does not bind the target, we can only conclude that target
       is not free if it is not free in all the composition's arguments. */
    for (size_t i = 0; i < ARR_LENGTH(context->expression->bindings); ++i)
    {
      const Value *binding = *ARR_GET(context->expression->bindings, i);
      if (values_equal(target, binding))
        return TRUE;
    }

    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      const Value *arg = *ARR_GET(context->arguments, i);
      if (!not_free_in_env(env, target, arg))
        return FALSE;
    }
    return TRUE;
  }
  else if (context->value_type == ValueTypeVariable)
  {
    /* There is no way to know if there haven't been requirements imposed
       already. */
    /* TODO: if the type is atomic, and we know the target and the context
       are required to be distinct, we can safely return true. */
    return FALSE;
  }
  else
  {
    /* If we made it this far, we have a constant distinct from the target.
       The target does not occur in the context, so it does not occur free
       in the context. */
    return TRUE;
  }
}

static bool
evaluate_not_free(sl_LogicState *state, const struct ProofEnvironment *env,
  ValueArray args)
{
  const Value *target, *context;
  if (ARR_LENGTH(args) != 2)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  target = *ARR_GET(args, 0);
  context = *ARR_GET(args, 1);

  return not_free_in_env(env, target, context);
}

/* --- Not Bound --- */
static bool
evaluate_not_bound(struct sl_LogicState *state,
  const struct ProofEnvironment *env, ValueArray args)
{
  #if 0
  const Value *target, *context;
  if (ARR_LENGTH(args) != 2)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  target = *ARR_GET(args, 0);
  context = *ARR_GET(args, 1);

  /* TODO: Instead of requiring everything to be terminal, in cases that
     we have non-terminals, figure out what must be required in order to
     make it work and check for that requirement in the environment. */
  if (!value_terminal(target) || !value_terminal(context))
    return FALSE;

  {
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
  #endif
  return TRUE;
}

/* --- Free --- */
static bool
evaluate_free(sl_LogicState *state, const struct ProofEnvironment *env,
  ValueArray args)
{
  const Value *target, *context;
  if (ARR_LENGTH(args) != 2)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  target = *ARR_GET(args, 0);
  context = *ARR_GET(args, 1);

  return FALSE;
}

/* --- Bound --- */
static bool
evaluate_bound(sl_LogicState *state, const struct ProofEnvironment *env,
  ValueArray args)
{
  const Value *target, *context;
  if (ARR_LENGTH(args) != 2)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  target = *ARR_GET(args, 0);
  context = *ARR_GET(args, 1);

  return FALSE;
}

/* --- Cover Free --- */
static bool
cover_free_in_env(const struct ProofEnvironment *env, ValueArray covering,
  const Value *context)
{
  /* Check if there is a corresponding requirement in the environment. */
  for (size_t i = 0; i < ARR_LENGTH(env->requirements); ++i)
  {
    const struct Requirement *req = ARR_GET(env->requirements, i);
    if (req->type == RequirementTypeCoverFree)
    {
      /* TODO: we only need to show that covering is a subset of the
         covering set in the other requirement. */
      const Value *r_context;
      bool can_match = TRUE;
      if (ARR_LENGTH(covering) != ARR_LENGTH(req->arguments) - 1)
        continue;
      for (size_t j = 0; j < ARR_LENGTH(covering); ++j)
      {
        const Value *cover, *r_cover;
        cover = *ARR_GET(covering, j);
        r_cover = *ARR_GET(req->arguments, j);
        if (!values_equal(cover, r_cover))
        {
          can_match = FALSE;
          break;
        }
      }
      if (!can_match)
        continue;
      r_context = *ARR_GET(req->arguments, ARR_LENGTH(covering));
      if (values_equal(context, r_context))
        return TRUE;
    }
  }

  for (size_t i = 0; i < ARR_LENGTH(covering); ++i)
  {
    const Value *cover = *ARR_GET(covering, i);
    if (values_equal(cover, context))
      return TRUE;
  }

  if (context->value_type == ValueTypeConstant
    || context->value_type == ValueTypeVariable)
  {
    if (value_gets_bound(context, context))
      return TRUE;
  }

  if (context->value_type == ValueTypeComposition)
  {
    for (size_t i = 0; i < ARR_LENGTH(context->arguments); ++i)
    {
      const Value *arg = *ARR_GET(context->arguments, i);
      if (!cover_free_in_env(env, covering, arg))
        return FALSE;
    }
    return TRUE;
  }
  else if (context->value_type == ValueTypeConstant)
  {
    if (!context->type->binds)
      return TRUE;
  }

  //printf("aw %s\n", string_from_value(context));
  return FALSE;
}

static bool
evaluate_cover_free(sl_LogicState *state,
  const struct ProofEnvironment *env, ValueArray args)
{
  ValueArray covering;
  const Value *context;
  if (ARR_LENGTH(args) < 1)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }

  ARR_INIT(covering);
  for (size_t i = 0; i < ARR_LENGTH(args) - 1; ++i)
  {
    ARR_APPEND(covering, *ARR_GET(args, i));
  }
  context = *ARR_GET(args, ARR_LENGTH(args) - 1);
  return cover_free_in_env(env, covering, context);
}

/* --- Cover Bound --- */
static bool
evaluate_cover_bound(sl_LogicState *state,
  const struct ProofEnvironment *env, ValueArray args)
{
  return FALSE;
}

/* --- Substitution --- */
static bool
is_substitution(const struct ProofEnvironment *env, const Value *target,
  const Value *context, const Value *source, const Value *new_context)
{
  /* Doing nothing is always a substitution (but not a full substitution,
     unless there are no occurences of target in context). */
  if (values_equal(context, new_context))
    return TRUE;
  if (values_equal(target, source) && values_equal(context, new_context))
    return TRUE;

  /* Check if there is a corresponding requirement in the environment. */
  for (size_t i = 0; i < ARR_LENGTH(env->requirements); ++i)
  {
    const struct Requirement *req = ARR_GET(env->requirements, i);
    if (req->type == RequirementTypeSubstitution)
    {
      const Value *r_target, *r_context, *r_source, *r_new_context;
      r_target = *ARR_GET(req->arguments, 0);
      r_context = *ARR_GET(req->arguments, 1);
      r_source = *ARR_GET(req->arguments, 2);
      r_new_context = *ARR_GET(req->arguments, 3);
      if (values_equal(target, r_target) && values_equal(context, r_context)
        && values_equal(source, r_source)
        && values_equal(new_context, r_new_context))
        return TRUE;
    }
  }

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
      if (!is_substitution(env, target, ctx_arg, source, new_ctx_arg))
        return FALSE;
    }
    return TRUE;
  }
  else
  {
    /* If there is nothing that can be substituted in the tree, they must
       be equal. */
    if (values_equal(context, new_context))
      return TRUE;
    else
      return FALSE;
  }
}

static bool
evaluate_substitution(sl_LogicState *state,
  const struct ProofEnvironment *env, ValueArray args)
{
  const Value *target, *context, *source, *new_context;
  if (ARR_LENGTH(args) != 4)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  target = *ARR_GET(args, 0);
  context = *ARR_GET(args, 1);
  source = *ARR_GET(args, 2);
  new_context = *ARR_GET(args, 3);

  return is_substitution(env, target, context, source, new_context);
}

/* --- Full Substitution --- */
static bool
is_full_substitution(const struct ProofEnvironment *env, const Value *target,
  const Value *context, const Value *source, const Value *new_context)
{
  /* As a special case that doesn't (and cannot) require evaluation,
     always return true when performing the identity substitution. */
  if (values_equal(target, source) && values_equal(context, new_context))
    return TRUE;

  /* Check if there is a corresponding requirement in the environment. */
  for (size_t i = 0; i < ARR_LENGTH(env->requirements); ++i)
  {
    const struct Requirement *req = ARR_GET(env->requirements, i);
    if (req->type == RequirementTypeFullSubstitution)
    {
      const Value *r_target, *r_context, *r_source, *r_new_context;
      r_target = *ARR_GET(req->arguments, 0);
      r_context = *ARR_GET(req->arguments, 1);
      r_source = *ARR_GET(req->arguments, 2);
      r_new_context = *ARR_GET(req->arguments, 3);
      if (values_equal(target, r_target) && values_equal(context, r_context)
        && values_equal(source, r_source)
        && values_equal(new_context, r_new_context))
        return TRUE;
    }
  }

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
      if (!is_full_substitution(env, target, ctx_arg, source, new_ctx_arg))
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
evaluate_full_substitution(struct sl_LogicState *state,
  const struct ProofEnvironment *env, ValueArray args)
{
  const Value *target, *context, *source, *new_context;
  if (ARR_LENGTH(args) != 4)
  {
    LOG_NORMAL(state->log_out,
      "Requirement has wrong number of arguments");
    return 1;
  }
  target = *ARR_GET(args, 0);
  context = *ARR_GET(args, 1);
  source = *ARR_GET(args, 2);
  new_context = *ARR_GET(args, 3);

  return is_full_substitution(env, target, context, source, new_context);
}

/* --- Evaluation --- */
bool
evaluate_requirement(sl_LogicState *state, const struct Requirement *req,
  ArgumentArray environment_args, const struct ProofEnvironment *env)
{
  bool satisfied = FALSE;
  ValueArray instantiated_args;

  ARR_INIT(instantiated_args);
  for (size_t j = 0; j < ARR_LENGTH(req->arguments); ++j)
  {
    const Value *arg = *ARR_GET(req->arguments, j);
    Value *instantiated_0 = instantiate_value(arg, environment_args);
    Value *instantiated = reduce_expressions(instantiated_0);
    ARR_APPEND(instantiated_args, instantiated);
  }

  switch (req->type)
  {
    case RequirementTypeDistinct:
      satisfied = evaluate_distinct(state, env, instantiated_args);
      break;
    case RequirementTypeFreeFor:
      satisfied = evaluate_free_for(state, env, instantiated_args);
      break;
    case RequirementTypeNotFree:
      satisfied = evaluate_not_free(state, env, instantiated_args);
      break;
    case RequirementTypeNotBound:
      satisfied = evaluate_not_bound(state, env, instantiated_args);
      break;
    case RequirementTypeFree:
      satisfied = evaluate_free(state, env, instantiated_args);
      break;
    case RequirementTypeBound:
      satisfied = evaluate_bound(state, env, instantiated_args);
      break;
    case RequirementTypeCoverFree:
      satisfied = evaluate_cover_free(state, env, instantiated_args);
      break;
    case RequirementTypeCoverBound:
      satisfied = evaluate_cover_bound(state, env, instantiated_args);
      break;
    case RequirementTypeSubstitution:
      satisfied = evaluate_substitution(state, env, instantiated_args);
      break;
    case RequirementTypeFullSubstitution:
      satisfied = evaluate_full_substitution(state, env, instantiated_args);
      break;
  }
  ARR_FREE(instantiated_args);
  return satisfied;
}
