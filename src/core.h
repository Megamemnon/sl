#ifndef CORE_H
#define CORE_H

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
  const SymbolPath *path;

  bool atomic;
};

struct Constant
{
  uint32_t id;
  const SymbolPath *path;
  const struct Type *type;
};

struct Expression
{
  uint32_t id;
  const SymbolPath *path;

  const struct Type *type;
  Array parameters;
  Array bindings;
};

enum ValueType
{
  ValueTypeConstant,
  ValueTypeVariable,
  ValueTypeComposition
};

struct Value
{
  enum ValueType value_type;
  const struct Type *type;

  /* TODO: use a union? */
  char *variable_name;
  const struct Constant *constant;
  bool bound;
  const struct Expression *expression;
  Array arguments;
};

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
  Array arguments;
};

struct Theorem
{
  uint32_t id;
  const SymbolPath *path;
  bool is_axiom;

  Array parameters;
  Array requirements;
  Array assumptions;
  Array inferences;
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
  Array symbol_table;
  uint32_t next_id;

  FILE *log_out;
};

#endif
