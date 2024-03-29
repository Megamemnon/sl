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

struct sl_SymbolPath
{
  ARR(uint32_t) segments;
};

struct Parameter
{
  uint32_t name_id;
  uint32_t type_id;
};

const char * logic_state_get_string(const sl_LogicState *state,
    uint32_t index);

sl_LogicError sl_logic_get_symbol_id(const sl_LogicState *state,
    const sl_SymbolPath *path, uint32_t *id);

sl_LogicSymbol * sl_logic_get_symbol_by_id(sl_LogicState *state,
    uint32_t id);

const sl_SymbolPath * sl_logic_get_symbol_path_by_id(
    const sl_LogicState *state, uint32_t id);

struct Type
{
  uint32_t id;
  const sl_SymbolPath *path;

  bool atomic;
  bool binds;
  bool dummies;
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
  const sl_SymbolPath *path;
  uint32_t type_id;
  char *latex_format;
};

struct Constspace
{
  uint32_t id;
  uint32_t type_id;
};

struct sl_Parameter {
  uint32_t name_id;
  const struct Type *type;
};

struct sl_ParametrizedBlock {
  ARR(struct sl_Parameter) parameters;
};

struct Expression
{
  uint32_t id;
  const sl_SymbolPath *path;

  uint32_t type_id;
  ARR(struct Parameter) parameters;
  ARR(Value *) bindings;
  Value *replace_with;

  bool has_latex;
  struct LatexFormat latex;
};

enum ValueType
{
  ValueTypeConstant,
  ValueTypeVariable,
  ValueTypeComposition,
  ValueTypeDummy
};

typedef ARR(Value *) ValueArray;

struct Value
{
  enum ValueType value_type;
  uint32_t type_id; /* TODO: this should be computed. */
  Value *parent;

  union {
    uint32_t dummy_id;
    uint32_t variable_name_id;
    struct {
      sl_SymbolPath *constant_path;
      const char *constant_latex;
    } constant;
    struct {
      uint32_t expression_id;
      ValueArray arguments;
    } composition;
  } content;
};

struct Argument
{
  uint32_t name_id;
  Value *value;
};
typedef ARR(struct Argument) ArgumentArray;

/* Value methods. */
void
copy_value_to(Value *dst, const Value *src);

void
enumerate_value_occurrences(const Value *target, const Value *search_in,
  ValueArray *occurrences);

unsigned int
count_value_occurrences(const Value *target, const Value *search_in);

Value * reduce_expressions(const sl_LogicState *state, const Value *value);

Value *
instantiate_value(const Value *src, ArgumentArray args);

enum RequirementType
{
  RequirementTypeDistinct,
  RequirementTypeFreeFor,
  RequirementTypeNotFree,
  RequirementTypeCoverFree,
  RequirementTypeSubstitution,
  RequirementTypeFullSubstitution,
  RequirementTypeUnused
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
  const sl_SymbolPath *path;
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

struct sl_LogicSymbol
{
  sl_SymbolPath *path;
  uint32_t id;
  sl_LogicSymbolType type;
  void *object;
};

struct sl_LogicState
{
  ARR(char *) string_table;
  ARR(sl_LogicSymbol) symbol_table;
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
