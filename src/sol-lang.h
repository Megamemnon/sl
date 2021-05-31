#ifndef SOL_LANG_H
#define SOL_LANG_H

#include "lex.h"
#include "parse.h"

int
sol_verify(const char *file_path);

enum SolASTNodeType
{
  NodeTypeUnidentified = 0,
  NodeTypeNamespace,
  NodeTypeImport,
  NodeTypeIdentifierPath,
  NodeTypeIdentifierPathSegment,
  NodeTypeAxiom,
  NodeTypeHypothesis,
  NodeTypeInfer,
  NodeTypeFormula,
  NodeTypeFormulaExpression,
  NodeTypeTheorem,
  NodeTypeLet,
  NodeTypeStep,
  NodeTypeSubstitutionMap,
  NodeTypeSubstitution,
  NodeTypeParameterList,
  NodeTypeParameter
};

struct SolASTNodeData
{
  enum SolASTNodeType type;

  char *name;
  char *data_type;
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
parse_namespace_interior(struct ParserState *state);

int
parse_import(struct ParserState *state);

int
parse_identifier_path(struct ParserState *state);

int
parse_formula(struct ParserState *state);

int
parse_formula_expression(struct ParserState *state);

int
parse_axiom(struct ParserState *state);

int
parse_hypothesis(struct ParserState *state);

int
parse_infer(struct ParserState *state);

int
parse_theorem(struct ParserState *state);

int
parse_let(struct ParserState *state);

int
parse_step(struct ParserState *state);

int
parse_substitution_map(struct ParserState *state);

int
parse_substitution(struct ParserState *state);

int
parse_parameter_list(struct ParserState *state);

int
parse_parameter(struct ParserState *state);

void
print_sol_node(char *buf, size_t len, const struct ASTNode *node);

enum ParameterType
{
  ParameterTypeFormula = 0,
  ParameterTypeVar
};

struct Parameter
{
  char *name;
  enum ParameterType type;
};

struct Formula
{
  char *global_name;

  struct Parameter *parameters;
  size_t parameters_n;

  struct ASTNode *expression; /* NULL if the formula is atomic. */
};

struct Hypothesis
{
  char *name;
  struct ASTNode *expression;
};

struct Axiom
{
  char *global_name;

  struct Parameter *parameters;
  size_t parameters_n;

  struct Hypothesis *hypotheses;
  size_t hypotheses_n;

  struct ASTNode *infer;
};

struct Theorem
{
  char *global_name;

  struct Parameter *parameters;
  size_t parameters_n;

  struct Hypothesis *hypotheses;
  size_t hypotheses_n;

  struct ASTNode *infer;
};

struct ValidationState
{
  const struct ParserState *input;

  struct Formula *formulas;
  size_t formulas_n;

  struct Axiom *axioms;
  size_t axioms_n;

  struct Theorem *theorems;
  size_t theorems_n;
};

void
traverse_tree_for_formulas(const struct ASTNode *node, void *userdata);

int
validate_new_formula(const struct ValidationState *state,
  const struct Formula *formula);

void
traverse_tree_for_axioms(const struct ASTNode *node, void *userdata);

void
traverse_tree_for_theorems(const struct ASTNode *node, void *userdata);

int
validate_program(struct ValidationState *state);

#endif
