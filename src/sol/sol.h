/*

TODO:
- Verify that judgements are declared before being used.

LANGUAGE DESCRIPTION:

- BUILTINS
-- `is_not_subexpression([A], [B])`

   This judgement is true when `[B]` does not contain any instances of `[A]`
   as a subexpression.

-- `is_substitution([A], [B], [TARGET_EXPR], [SOURCE_EXPR])`

   This judgement is true when `[TARGET_EXPR]` can be formed
   from `[SOURCE_EXPR]` by replacing some occurrences of `[B]` with `[A]`.

-- `is_full_substitution([A], [B], [TARGET_EXPR], [SOURCE_EXPR])`

   This judgement is true when `[TARGET_EXPR]` is formed from `[SOURCE_EXPR]`
   by replacing all occurrences of `[B]` with `[A]`.

*/
#ifndef SOL_H
#define SOL_H

#include <lex.h>
#include <parse.h>

int
sol_verify(const char *file_path);

enum SolASTNodeType
{
  NodeTypeUnidentified = 0,
  NodeTypeNamespace,
  NodeTypeImport,

  NodeTypeJudgement,
  NodeTypeAxiom,
  NodeTypeTheorem,

  NodeTypeAssume,
  NodeTypeInfer,
  NodeTypeStep,
  NodeTypeDef,

  NodeTypeJudgementExpression,
  NodeTypeInferenceExpression,
  NodeTypeExpression,
  NodeTypeExpressionConstant,
  NodeTypeExpressionVariable,
  NodeTypeExpressionPlaceholder,

  NodeTypeIdentifierPath,
  NodeTypeIdentifierPathSegment,
  NodeTypeParameterList,
  NodeTypeParameter,
  NodeTypeArgumentList
};

/* Parser Methods */
struct SolASTNodeData
{
  enum SolASTNodeType type;

  const struct Token *location;
  char *name;
};

void
free_sol_node(struct ASTNode *node);

void
copy_sol_node(struct ASTNode *dst, const struct ASTNode *src);

void
init_sol_node(struct ASTNode *node);

struct SolASTNodeData *
get_sol_node_data(struct ASTNode *node);

const struct SolASTNodeData *
get_sol_node_data_c(const struct ASTNode *node);

int
parse_program(struct ParserState *state);

int
parse_namespace(struct ParserState *state);

int
parse_import(struct ParserState *state);

int
parse_judgement(struct ParserState *state);

int
parse_axiom(struct ParserState *state);

int
parse_theorem(struct ParserState *state);

int
parse_assume(struct ParserState *state);

int
parse_infer(struct ParserState *state);

int
parse_step(struct ParserState *state);

int
parse_def(struct ParserState *state);

int
parse_judgement_expression(struct ParserState *state);

int
parse_inference_expression(struct ParserState *state);

int
parse_expression(struct ParserState *state);

int
parse_identifier_path(struct ParserState *state);

int
parse_parameter_list(struct ParserState *state);

int
parse_argument_list(struct ParserState *state);

void
print_sol_node(char *buf, size_t len, const struct ASTNode *node);

/* Validation Methods */
struct Expression
{
  Array symbols;
};

enum ExpressionSymbolType
{
  ExpressionSymbolTypeConstant = 0,
  ExpressionSymbolTypeVariable,
  ExpressionSymbolTypePlaceholder
};

struct ExpressionSymbol
{
  char *value;
  enum ExpressionSymbolType type;
};

void
free_expression_symbol(struct ExpressionSymbol *symbol);

void
free_expression(struct Expression *expression);

int
copy_expression_symbol(struct ExpressionSymbol *dst,
  const struct ExpressionSymbol *src);

int
copy_expression(struct Expression *dst, const struct Expression *src);

char *
expression_to_string(const struct Expression *expr);

struct Parameter
{
  char *name;
};

enum SolObjectType
{
  SolObjectTypeNone = 0,
  SolObjectTypeJudgement,
  SolObjectTypeTheorem
};

struct SolObject
{
  enum SolObjectType type;

  Array parameters;
  Array assumptions;
  Array inferences;
};

struct JudgementInstance
{
  const struct SolObject *judgement;
  Array expression_args;

  const struct Token *location;
};

char *
judgement_instance_to_string(const struct JudgementInstance *inst);

struct ObjectName
{
  Array segments; /* (char *) */
};

void
free_name(struct ObjectName *path);

int
extract_path(struct ObjectName *path, const struct ASTNode *identifier_path);

char *
name_to_string(const struct ObjectName *name);

struct ProofEnv
{
  Array proven;
};

struct Argument
{
  char *name;
  struct Expression value;
};

struct ArgumentList
{
  Array arguments; // Expressions
};

struct Symbol
{
  char *name;
  struct SolObject *object;
};

struct SolScopeNodeData
{
  char *name;
  Array symbol_table;
  Array symbol_search_locations;
};

void
free_scope_node(struct ASTNode *node);

void
copy_scope_node(struct ASTNode *dst, const struct ASTNode *src);

void
init_scope_node(struct ASTNode *node);

/* TODO: Lookup by path, not just a string. */
struct SolObject *
lookup_symbol(struct ASTNode *scope, const struct ObjectName *path);

struct SolScopeNodeData *
get_scope_node_data(struct ASTNode *node);

const struct SolScopeNodeData *
get_scope_node_data_c(const struct ASTNode *node);

struct ValidationState
{
  struct CompilationUnit *unit;

  const struct ParserState *input;

  struct ASTNode scope_tree_root;
  struct ASTNode *scope_current;
};

int
validate_expression(struct ValidationState *state,
  struct Expression *dst,
  const struct ASTNode *ast_expression,
  const struct SolObject *env,
  int depth);

int
validate_assume(struct ValidationState *state,
  const struct ASTNode *ast_assume,
  struct SolObject *env);

int
validate_infer(struct ValidationState *state,
  const struct ASTNode *ast_infer,
  struct SolObject *env);

int
validate_import(struct ValidationState *state,
  const struct ASTNode *ast_import);

int
validate_judgement(struct ValidationState *state,
  const struct ASTNode *ast_judgement);

int
validate_axiom(struct ValidationState *state,
  const struct ASTNode *ast_axiom);

int
substitute_into_expression(struct ValidationState *state,
  struct Expression *dst, const struct Expression *expr,
  const struct ArgumentList *args);

bool
symbols_equal(const struct ExpressionSymbol *a,
  const struct ExpressionSymbol *b);

bool
expressions_equal(const struct Expression *a, const struct Expression *b);

int
instantiate_object(struct ValidationState *state, const struct SolObject *obj,
  const struct ArgumentList *args, struct ProofEnv *env);

bool
judgement_proved(struct ValidationState *state, const struct ProofEnv *env,
  const struct JudgementInstance *judgement);

int
validate_theorem(struct ValidationState *state,
  const struct ASTNode *ast_theorem);

int
validate_namespace(struct ValidationState *state,
  const struct ASTNode *ast_namespace);

int
validate_program(struct ValidationState *state);

#endif
