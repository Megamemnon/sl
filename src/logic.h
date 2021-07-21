#ifndef LOGIC_H
#define LOGIC_H

#include "common.h"
#include <stdio.h>

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

const char *
get_symbol_path_segment(const SymbolPath *path, size_t index);

const char *
get_symbol_path_last_segment(const SymbolPath *path);

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
new_logic_state(FILE *log_out);

void
free_logic_state(LogicState *state);

bool
logic_state_path_occupied(const LogicState *state, const SymbolPath *path);

SymbolPath *
find_first_occupied_path(const LogicState *state, SymbolPath **paths); /* NULL-terminated list. */

enum LogicError
{
  LogicErrorNone = 0,
  LogicErrorSymbolAlreadyExists
};
typedef enum LogicError LogicError;

/* Types. */
struct PrototypeType
{
  SymbolPath *type_path;
  bool atomic;
};

LogicError
add_type(LogicState *state, struct PrototypeType proto);

struct PrototypeConstant
{
  SymbolPath *constant_path;
  SymbolPath *type_path;
};

LogicError
add_constant(LogicState *, struct PrototypeConstant proto);

struct Value;
typedef struct Value Value;

/* Expressions. */
struct PrototypeParameter
{
  char *name;
  SymbolPath *type;
};

struct PrototypeExpression
{
  SymbolPath *expression_path;
  SymbolPath *expression_type;
  struct PrototypeParameter **parameters; /* NULL-terminated list. */
  Value **bindings; /* NULL-terminated list. */
};

/* TODO: The return value should be a struct, or modify the PrototypeExpression,
   in order to propagate errors with full detail. */
LogicError
add_expression(LogicState *state, struct PrototypeExpression expression);

/* Methods to manipulate values. */
void
free_value(Value *value);

Value *
copy_value(const Value *value);

bool
values_equal(const Value *a, const Value *b);

/* True iff all the variables in the expression have atomic types. */
bool
value_terminal(const Value *v);

char *
string_from_value(const Value *value);

Value *
new_variable_value(LogicState *state, const char *name, const SymbolPath *type);

Value *
new_constant_value(LogicState *state, const SymbolPath *constant);

Value *
new_composition_value(LogicState *state, const SymbolPath *expr_path,
  Value * const *args); /* `args` is a NULL-terminated list. */

struct PrototypeProofStep
{
  SymbolPath *theorem_path;
  Value **arguments; /* NULL-terminated list. */
};

struct PrototypeRequirement
{
  char *require;
  Value **arguments; /* NULL-terminated list. */
};

struct PrototypeTheorem
{
  SymbolPath *theorem_path;
  struct PrototypeParameter **parameters; /* NULL-terminated list. */
  struct PrototypeRequirement **requirements; /* NULL-terminated list. */
  Value **assumptions; /* NULL-terminated list. */
  Value **inferences; /* NULL-terminated list. */
  struct PrototypeProofStep **steps; /* NULL-terminated list, disregarded for axioms. */
};

/* TODO: The return value should be a struct, or modify the PrototypeTheorem,
   in order to propagate errors with full detail. */
LogicError
add_axiom(LogicState *state, struct PrototypeTheorem axiom);

/* TODO: The return value should be a struct, or modify the PrototypeTheorem,
   in order to propagate errors with full detail. */
LogicError
add_theorem(LogicState *state, struct PrototypeTheorem theorem);

#endif
