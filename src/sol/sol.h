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

struct ObjectNameSegment
{
  char *name;
};

struct ObjectName
{
  Array segments;
};

struct Substitution
{
  char *dst;
  char *src;
};

struct Symbol
{
  char *value;
  int is_variable;
  Array substitutions;
};

struct Expression
{
  Array symbols;
};

struct Judgement
{
  struct ObjectName name;
  size_t parameters_n;
};

struct Parameter
{
  char *name;
};

/* No need to distinguish axioms and theorems after theorems are verified. */
struct Theorem
{
  struct ObjectName name;

  Array parameters;
  Array assumptions;
  struct Judgement infer;
};

struct ValidationState
{
  const struct ParserState *input;
  struct ObjectName current_scope;
  Array judgements;
  Array theorems;
};

int
names_equal(const struct ObjectName *a, const struct ObjectName *b);

int
name_used(struct ValidationState *state,
  const struct ObjectName *name);

char *
name_to_string(const struct ObjectName *name);

int
validate_import(struct ValidationState *state,
  const struct ASTNode *import);

int
validate_judgement(struct ValidationState *state,
  const struct ASTNode *judgement);

int
validate_assume(struct ValidationState *state,
  const struct ASTNode *assume,
  const struct Theorem *env);

int
validate_infer(struct ValidationState *state,
  const struct ASTNode *infer,
  const struct Theorem *env);

int
validate_axiom(struct ValidationState *state,
  const struct ASTNode *axiom);

int
validate_namespace(struct ValidationState *state,
  const struct ASTNode *namespace);

int
validate_program(struct ValidationState *state);

#endif
