#ifndef LOGIC_H
#define LOGIC_H

#include <common.h>

/* Methods to manipulate paths. */
struct SymbolPath;
typedef struct SymbolPath SymbolPath;

SymbolPath *
init_symbol_path();

SymbolPath *
copy_symbol_path(const SymbolPath *src);

void
free_symbol_path(SymbolPath *path);

int
length_of_symbol_path(const SymbolPath *path);

char *
string_from_symbol_path(const SymbolPath *path);

void
push_symbol_path(SymbolPath *path, const char *segment);

void
pop_symbol_path(SymbolPath *path);

void
append_symbol_path(SymbolPath *path, const SymbolPath *to_append);

bool
symbol_paths_equal(const SymbolPath *a, const SymbolPath *b);

/* Functions for manipulating the logic state, which contains all the theorems,
   expressions, etc. that are handled. */
struct LogicState;
typedef struct LogicState LogicState;

LogicState *
new_logic_state();

void
free_logic_state(LogicState *state);

enum LogicError
{
  LogicErrorNone = 0,
  LogicErrorSymbolAlreadyExists
};
typedef enum LogicError LogicError;

LogicError
add_type(LogicState *state, const SymbolPath *type);

struct PrototypeParameter
{
  const char *name;
  const SymbolPath *type;
};

struct PrototypeExpression
{
  const SymbolPath *expression_path;
  const SymbolPath *expression_type;
  const struct PrototypeParameter *parameters; /* NULL-terminated list. */
};

/* TODO: The return value should be a struct, or modify the PrototypeExpression,
   in order to propagate errors with full detail. */
LogicError
add_expression(LogicState *state, struct PrototypeExpression expression);



#if 0
/* There is no reason to differentiate between axioms and theorems that have
   been proven, so the verifier refers to these both as "theorems". */
enum SymbolType
{
  SymbolTypeNone = 0,
  SymbolTypeType,
  SymbolTypeExpression,
  SymbolTypeTheorem
};

struct ObjectType;
typedef struct ObjectType ObjectType;

bool
types_equal(const ObjectType *a, const ObjectType *b);

void
free_type(ObjectType *type);

struct Parameter;
typedef struct Parameter Parameter;

Parameter *
copy_parameter(const Parameter *src);

void
free_parameter(Parameter *param);

struct ObjectExpression;
typedef struct ObjectExpression ObjectExpression;

void
free_expression(ObjectExpression *expr);

enum ValueType
{
  ValueTypeComposition,
  ValueTypeConstant,
  ValueTypeVariable
};

struct Value;
typedef struct Value Value;

bool
values_equal(const Value *a, const Value *b);

char *
string_from_value(const Value *value);

Value *
copy_value(const Value *src);

void
free_value(Value *value);

struct ObjectTheorem;
typedef struct ObjectTheorem ObjectTheorem;

void
free_theorem(ObjectTheorem *theorem);

struct Symbol;
typedef struct Symbol Symbol;

void
free_symbol(Symbol *sym);
#endif

#endif
