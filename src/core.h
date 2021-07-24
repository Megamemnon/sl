#ifndef CORE_H
#define CORE_H

#include "common.h"
#include "logic.h"

#define LOG_NORMAL(out, ...) \
do { \
  fprintf(out, __VA_ARGS__); \
} \
while (0);

#define LOG_VERBOSE(out, ...) \
do { \
  if (verbose) \
    fprintf(out, __VA_ARGS__); \
} \
while (0);

struct SymbolPath
{
  ARR(char *) segments;
};

struct Parameter
{
  char *name;
  const struct Type *type;
};

struct Type
{
  uint32_t id;
  const SymbolPath *path;

  bool atomic;
};

struct LatexFormatSegment
{
  bool is_variable;
  char *string;
};

struct LatexFormat
{
  ARR(struct LatexFormatSegment) segments;
};

struct Constant
{
  uint32_t id;
  const SymbolPath *path;
  const struct Type *type;

  bool has_latex;
  struct LatexFormat latex;
};

struct Expression
{
  uint32_t id;
  const SymbolPath *path;

  const struct Type *type;
  ARR(struct Parameter) parameters;
  ARR(Value *) bindings;

  bool has_latex;
  struct LatexFormat latex;
};

enum ValueType
{
  ValueTypeConstant,
  ValueTypeVariable,
  ValueTypeComposition
};

typedef ARR(Value *) ValueArray;

struct Value
{
  enum ValueType value_type;
  const struct Type *type;

  /* TODO: use a union? */
  char *variable_name;
  const struct Constant *constant;
  bool bound;
  const struct Expression *expression;
  ValueArray arguments;
};

struct Argument
{
  char *name;
  Value *value;
};
typedef ARR(struct Argument) ArgumentArray;

/* Value methods. */
void
copy_value_to(Value *dst, const Value *src);

void
enumerate_value_occurrences(const Value *target, const Value *search_in,
  ValueArray *occurrences);

Value *
instantiate_value(struct LogicState *state, const Value *src, ArgumentArray args);

enum RequirementType
{
  RequirementTypeFreeFor,
  RequirementTypeNotFree,
  RequirementTypeSubstitution,
  RequirementTypeFullSubstitution
};

struct Requirement
{
  enum RequirementType type;
  ValueArray arguments;
};

struct Theorem;

struct TheoremReference
{
  struct Theorem *theorem;
  ValueArray arguments;
};

struct Theorem
{
  uint32_t id;
  const SymbolPath *path;
  bool is_axiom;

  ARR(struct Parameter) parameters;
  ARR(struct Requirement) requirements;
  ValueArray assumptions;
  ValueArray inferences;
  ARR(struct TheoremReference) steps;
};

enum SymbolType
{
  SymbolTypeType,
  SymbolTypeConstant,
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
  ARR(struct Symbol) symbol_table;
  uint32_t next_id;

  FILE *log_out;
};

bool
types_equal(const struct Type *a, const struct Type *b);

int
instantiate_theorem(struct LogicState *state,
  const struct Theorem *src, ArgumentArray args, ValueArray *proven, bool force);

/* Requirements. */
bool
evaluate_free_for(struct LogicState *state,
  const Value *source, const Value *target, const Value *context);

bool
evaluate_not_free(struct LogicState *state,
  const Value *target, const Value *context);

bool
evaluate_not_bound(struct LogicState *state,
  const Value *target, const Value *context);

bool
evaluate_free(struct LogicState *state,
  const Value *target, const Value *context);

bool
evaluate_bound(struct LogicState *state,
  const Value *target, const Value *context);

bool
evaluate_substitution(struct LogicState *state,
  const Value *target, const Value *context,
  const Value *source, const Value *new_context);

bool
evaluate_full_substitution(struct LogicState *state,
  const Value *target, const Value *context,
  const Value *source, const Value *new_context);

#endif
