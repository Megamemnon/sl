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

  NodeTypeJudgementExpression,
  NodeTypeInferenceExpression,
  NodeTypeExpression,
  NodeTypeExpressionConstant,
  NodeTypeExpressionVariable,

  NodeTypeSubstitutionMap,
  NodeTypeSubstitution,
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
parse_judgement_expression(struct ParserState *state);

int
parse_inference_expression(struct ParserState *state);

int
parse_expression(struct ParserState *state);

int
parse_expression_variable(struct ParserState *state);

int
parse_substitution_map(struct ParserState *state);

int
parse_substitution(struct ParserState *state);

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

struct Substitution
{
  char *dst;
  struct Expression *src;
};

struct ExpressionSymbol
{
  char *value;
  bool is_variable;
  Array substitutions;
};

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

struct JudgementInstance
{
  struct Judgement *judgement;

  Array expression_args;
};

struct SolObject
{
  enum SolObjectType type;

  Array parameters;
  Array assumptions;
  Array inferences;
};

struct ObjectNameSegment
{
  char *name;
};

struct ObjectName
{
  Array segments;
};

int
names_equal(const struct ObjectName *a, const struct ObjectName *b);

/*
int
name_used(struct ValidationState *state,
  const struct ObjectName *name);
*/

char *
name_to_string(const struct ObjectName *name);

struct Symbol
{
  char *name;
  struct SolObject *object;
};

struct SolScopeNodeData
{
  char *name;
  Array symbol_table;
  Array symbol_search_paths;
};

void
free_scope_node(struct ASTNode *node);

void
copy_scope_node(struct ASTNode *dst, const struct ASTNode *src);

void
init_scope_node(struct ASTNode *node);

struct SolScopeNodeData *
get_scope_node_data(struct ASTNode *node);

const struct SolScopeNodeData *
get_scope_node_data_c(const struct ASTNode *node);

struct ValidationState
{
  const struct ParserState *input;

  struct ASTNode scope_tree_root;
  struct ASTNode *scope_current;
};

struct Expression *
validate_expression(struct ValidationState *state,
  const struct ASTNode *ast_expression,
  const struct SolObject *env);

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
validate_namespace(struct ValidationState *state,
  const struct ASTNode *ast_namespace);

int
validate_program(struct ValidationState *state);

#endif
