#ifndef PARSE_H
#define PARSE_H

#include "common.h"
#include "logic.h"
#include <ctype.h>
#include <stdio.h>
#include <stdint.h>

typedef struct sl_LexerState sl_LexerState;

enum sl_LexerTokenType
{
  sl_LexerTokenType_None = 0,
  sl_LexerTokenType_Unknown,
  sl_LexerTokenType_LineEnd,
  sl_LexerTokenType_Identifier,
  sl_LexerTokenType_String,
  sl_LexerTokenType_Number,
  sl_LexerTokenType_LineComment,
  sl_LexerTokenType_OpeningBlockComment,
  sl_LexerTokenType_ClosingBlockComment,
  sl_LexerTokenType_OpeningParenthesis,
  sl_LexerTokenType_ClosingParenthesis,
  sl_LexerTokenType_OpeningBrace,
  sl_LexerTokenType_ClosingBrace,
  sl_LexerTokenType_OpeningAngle,
  sl_LexerTokenType_ClosingAngle,
  sl_LexerTokenType_OpeningBracket,
  sl_LexerTokenType_ClosingBracket,
  sl_LexerTokenType_Plus,
  sl_LexerTokenType_Dot,
  sl_LexerTokenType_Comma,
  sl_LexerTokenType_Semicolon,
  sl_LexerTokenType_Colon,
  sl_LexerTokenType_Percent,
  sl_LexerTokenType_DollarSign
};
typedef enum sl_LexerTokenType sl_LexerTokenType;

struct sl_LexerNumber
{
  bool is_number;
  uint32_t value;
};

sl_LexerState *
sl_lexer_new_state_from_file(FILE *input);

sl_LexerState *
sl_lexer_new_state_from_string(const char *input);

void
sl_lexer_free_state(sl_LexerState *state);

int
sl_lexer_advance(sl_LexerState *state);

sl_LexerTokenType
sl_lexer_get_current_token_type(const sl_LexerState *state);

struct sl_StringSlice
sl_lexer_get_current_token_string_value(const sl_LexerState *state);

struct sl_LexerNumber
sl_lexer_get_current_token_numerical_value(const sl_LexerState *state);

uint32_t
sl_lexer_get_current_token_line(const sl_LexerState *state);

uint32_t
sl_lexer_get_current_token_column(const sl_LexerState *state);

struct sl_StringSlice
sl_lexer_get_current_token_source(const sl_LexerState *state);

int
sl_lexer_clear_unused(sl_LexerState *state);

#include "lex.h"

enum sl_ASTNodeType
{
  sl_ASTNodeType_None = 0,
  sl_ASTNodeType_Namespace,
  sl_ASTNodeType_Use,
  sl_ASTNodeType_Type,
  sl_ASTNodeType_AtomicFlag,
  sl_ASTNodeType_BindsFlag,
  sl_ASTNodeType_ConstantDeclaration,
  sl_ASTNodeType_Expression,
  sl_ASTNodeType_Axiom,
  sl_ASTNodeType_Theorem,
  sl_ASTNodeType_ParameterList,
  sl_ASTNodeType_Parameter,
  sl_ASTNodeType_Latex,
  sl_ASTNodeType_Bind,
  sl_ASTNodeType_Def,
  sl_ASTNodeType_Assume,
  sl_ASTNodeType_Require,
  sl_ASTNodeType_Infer,
  sl_ASTNodeType_Step,
  sl_ASTNodeType_LatexString,
  sl_ASTNodeType_LatexVariable,
  sl_ASTNodeType_Composition,
  sl_ASTNodeType_Constant,
  sl_ASTNodeType_Variable,
  sl_ASTNodeType_Placeholder,
  sl_ASTNodeType_TheoremReference,
  sl_ASTNodeType_ArgumentList,
  sl_ASTNodeType_CompositionArgumentList,
  sl_ASTNodeType_Path,
  sl_ASTNodeType_PathSegment
};
typedef enum sl_ASTNodeType sl_ASTNodeType;

struct sl_ASTNode;
typedef struct sl_ASTNode sl_ASTNode;

const sl_ASTNode *
sl_node_get_parent(const sl_ASTNode *node);

size_t
sl_node_get_child_count(const sl_ASTNode *node);

const sl_ASTNode *
sl_node_get_child(const sl_ASTNode *node, size_t index);

sl_ASTNodeType
sl_node_get_type(const sl_ASTNode *node);

const struct Token *
sl_node_get_location(const sl_ASTNode *node);

const char *
sl_node_get_name(const sl_ASTNode *node);

const char *
sl_node_get_typename(const sl_ASTNode *node);

bool
sl_node_get_atomic(const sl_ASTNode *node);

sl_ASTNode *
sl_node_new();

void
free_tree(sl_ASTNode *root);

void
copy_tree(sl_ASTNode *dst, const sl_ASTNode *src);

void
sl_print_tree(const sl_ASTNode *root);

sl_ASTNode *
new_child(sl_ASTNode *parent);

typedef void (* traverse_node_callback_t)(const sl_ASTNode *, void *);

void
traverse_tree(const sl_ASTNode *root, traverse_node_callback_t node_callback,
  void *user_data);

struct ParserError
{
  char *error_msg;
  const struct Token *error_location;
};

struct ParserState
{
  struct CompilationUnit *unit;
  struct LexState *input;
  size_t token_index;

  sl_ASTNode *ast_root;
  sl_ASTNode *ast_current;
};

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

int
parse_root(struct ParserState *state);

sl_ASTNode *
sl_parse_input(sl_LexerState *input);

extern int verbose;

int
sl_verify(sl_LogicState *logic_state, const char *input_path, FILE *out);

#endif
