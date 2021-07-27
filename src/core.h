#ifndef CORE_H
#define CORE_H

#include "common.h"
#include "logic.h"

#define LOG_NORMAL(out, ...) \
do { \
  if (out != NULL) \
    fprintf(out, __VA_ARGS__); \
} \
while (0);

#define LOG_VERBOSE(out, ...) \
do { \
  if (out != NULL && verbose) \
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
  bool binds;
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
  const struct Expression *expression;
  ValueArray arguments;
  Value *parent;
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
instantiate_value(const Value *src, ArgumentArray args);

enum RequirementType
{
  RequirementTypeDistinct,
  RequirementTypeFreeFor,
  RequirementTypeNotFree,
  RequirementTypeNotBound,
  RequirementTypeFree,
  RequirementTypeBound,
  RequirementTypeCoverFree,
  RequirementTypeCoverBound,
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

struct ProofEnvironment
{
  ARR(struct Parameter) parameters;
  ARR(struct Requirement) requirements;
  ValueArray proven;
};

struct ProofEnvironment *
new_proof_environment();

void
free_proof_environment(struct ProofEnvironment *env);

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

struct sl_LogicState
{
  ARR(struct Symbol) symbol_table;
  uint32_t next_id;

  FILE *log_out;
};

bool
types_equal(const struct Type *a, const struct Type *b);

int
instantiate_theorem(struct sl_LogicState *state, const struct Theorem *src,
  ArgumentArray args, ValueArray *proven, bool force);

/* Requirements. */
int
make_requirement(sl_LogicState *state,
  struct Requirement *dst, const struct PrototypeRequirement *src);

bool
evaluate_requirement(sl_LogicState *state, const struct Requirement *req,
  ArgumentArray environment_args, const struct ProofEnvironment *env);

#endif
