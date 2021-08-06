#ifndef LOGIC_H
#define LOGIC_H

#include "common.h"
#include <stdio.h>

/* Methods to manipulate paths. */
typedef struct sl_SymbolPath sl_SymbolPath;

sl_SymbolPath *
sl_new_symbol_path();

sl_SymbolPath *
sl_copy_symbol_path(const sl_SymbolPath *src);

void
sl_free_symbol_path(sl_SymbolPath *path);

int
sl_get_symbol_path_length(const sl_SymbolPath *path);

const char *
sl_get_symbol_path_segment(const sl_SymbolPath *path, size_t index);

const char *
sl_get_symbol_path_last_segment(const sl_SymbolPath *path);

char *
sl_string_from_symbol_path(const sl_SymbolPath *path);

void
sl_push_symbol_path(sl_SymbolPath *path, const char *segment);

void
sl_pop_symbol_path(sl_SymbolPath *path);

void
sl_append_symbol_path(sl_SymbolPath *path, const sl_SymbolPath *to_append);

bool
sl_symbol_paths_equal(const sl_SymbolPath *a, const sl_SymbolPath *b);

/* Functions for manipulating the logic state, which contains all the theorems,
   expressions, etc. that are handled. */
typedef struct sl_LogicState sl_LogicState;

sl_LogicState *
sl_new_logic_state(FILE *log_out);

void
sl_free_logic_state(sl_LogicState *state);

bool
logic_state_path_occupied(const sl_LogicState *state, const sl_SymbolPath *path);

sl_SymbolPath *
find_first_occupied_path(const sl_LogicState *state, sl_SymbolPath **paths); /* NULL-terminated list. */

enum sl_LogicError
{
  sl_LogicError_None = 0,
  sl_LogicError_InvalidArgument,
  sl_LogicError_SymbolAlreadyExists,
  sl_LogicError_NoParent,
  sl_LogicError_CannotBindNonAtomic,
  sl_LogicError_NoType
};
typedef enum sl_LogicError sl_LogicError;

/* Symbols. */
typedef struct sl_LogicSymbol sl_LogicSymbol;

enum sl_LogicSymbolType
{
  sl_LogicSymbolType_Namespace,
  sl_LogicSymbolType_Type,
  sl_LogicSymbolType_Constant,
  sl_LogicSymbolType_Constspace,
  sl_LogicSymbolType_Expression,
  sl_LogicSymbolType_Theorem
};
typedef enum sl_LogicSymbolType sl_LogicSymbolType;

sl_LogicSymbol *
sl_logic_get_symbol(sl_LogicState *state, const sl_SymbolPath *path);

sl_LogicSymbolType
sl_get_symbol_type(const sl_LogicSymbol *symbol);

/* Namespaces. */
sl_LogicError
sl_logic_make_namespace(sl_LogicState *state,
  const sl_SymbolPath *namespace_path);

/* Types. */
sl_LogicError
sl_logic_make_type(sl_LogicState *state, const sl_SymbolPath *type_path,
  bool atomic, bool binds);

/* Constants. */
sl_LogicError
sl_logic_make_constant(sl_LogicState *state, const sl_SymbolPath *constant_path,
  const sl_SymbolPath *type_path, const char *latex_format);

struct Value;
typedef struct Value Value;

struct PrototypeLatexFormatSegment
{
  bool is_variable;
  char *string;
};

struct PrototypeLatexFormat
{
  struct PrototypeLatexFormatSegment **segments; /* NULL-terminated list. */
};

sl_LogicError
add_constspace(sl_LogicState *state, const sl_SymbolPath *space_path,
  const sl_SymbolPath *type_path);

/* Expressions. */
struct PrototypeParameter
{
  char *name;
  sl_SymbolPath *type;
};

struct PrototypeExpression
{
  sl_SymbolPath *expression_path;
  sl_SymbolPath *expression_type;
  struct PrototypeParameter **parameters; /* NULL-terminated list. */
  Value *replace_with; /* Optional - use NULL for an atomic expression. */
  Value **bindings; /* NULL-terminated list. */
  struct PrototypeLatexFormat latex;
};

/* TODO: The return value should be a struct, or modify the PrototypeExpression,
   in order to propagate errors with full detail. */
sl_LogicError
add_expression(sl_LogicState *state, struct PrototypeExpression expression);

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
new_variable_value(sl_LogicState *state, const char *name, const sl_SymbolPath *type);

Value *
new_constant_value(sl_LogicState *state, const sl_SymbolPath *constant);

Value *
new_composition_value(sl_LogicState *state, const sl_SymbolPath *expr_path,
  Value * const *args); /* `args` is a NULL-terminated list. */

struct PrototypeProofStep
{
  sl_SymbolPath *theorem_path;
  Value **arguments; /* NULL-terminated list. */
};

struct PrototypeRequirement
{
  char *require;
  Value **arguments; /* NULL-terminated list. */
};

struct PrototypeTheorem
{
  sl_SymbolPath *theorem_path;
  struct PrototypeParameter **parameters; /* NULL-terminated list. */
  struct PrototypeRequirement **requirements; /* NULL-terminated list. */
  Value **assumptions; /* NULL-terminated list. */
  Value **inferences; /* NULL-terminated list. */
  struct PrototypeProofStep **steps; /* NULL-terminated list, disregarded for axioms. */
};

/* TODO: The return value should be a struct, or modify the PrototypeTheorem,
   in order to propagate errors with full detail. */
sl_LogicError
add_axiom(sl_LogicState *state, struct PrototypeTheorem axiom);

/* TODO: The return value should be a struct, or modify the PrototypeTheorem,
   in order to propagate errors with full detail. */
sl_LogicError
add_theorem(sl_LogicState *state, struct PrototypeTheorem theorem);

#endif
