#ifndef PARSE_H
#define PARSE_H

#include "common.h"
#include "logic.h"
#include <ctype.h>
#include <stdio.h>
#include <stdint.h>

/* --- Text Input Interface --- */
typedef struct sl_TextInput sl_TextInput;

enum sl_MessageType
{
  sl_MessageType_Error,
  sl_MessageType_Warning,
  sl_MessageType_Note
};
typedef enum sl_MessageType sl_MessageType;

bool
sl_input_at_end(sl_TextInput *input);

char *
sl_input_gets(char *dst, size_t n, sl_TextInput *input);

sl_TextInput *
sl_input_from_file(const char *file_path);

sl_TextInput *
sl_input_from_string(const char *string);

void
sl_input_free(sl_TextInput *input);

void
sl_input_show_message(sl_TextInput *input, size_t line, size_t column,
  const char *message, sl_MessageType type);

/* --- Lexer --- */
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
sl_lexer_new_state_with_input(sl_TextInput *input);

void
sl_lexer_free_state(sl_LexerState *state);

int
sl_lexer_advance(sl_LexerState *state);

bool
sl_lexer_done(sl_LexerState *state);

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

void
sl_lexer_show_message_at_current_token(const sl_LexerState *state,
  const char *message, sl_MessageType type);

struct sl_StringSlice
sl_lexer_get_current_token_source(const sl_LexerState *state);

int
sl_lexer_clear_unused(sl_LexerState *state);

/* --- Parser --- */
enum sl_ASTNodeType
{
  sl_ASTNodeType_None = 0,
  sl_ASTNodeType_Namespace,
  sl_ASTNodeType_Import,
  sl_ASTNodeType_Use,
  sl_ASTNodeType_Type,
  sl_ASTNodeType_AtomicFlag,
  sl_ASTNodeType_BindsFlag,
  sl_ASTNodeType_ConstantDeclaration,
  sl_ASTNodeType_Constspace,
  sl_ASTNodeType_Expression,
  sl_ASTNodeType_ExpressionAs,
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

const char *
sl_node_get_name(const sl_ASTNode *node);

sl_ASTNode *
sl_node_new();

void
sl_node_free(sl_ASTNode *node);

void
sl_print_tree(const sl_ASTNode *root);

void
sl_node_show_message(sl_TextInput *input, const sl_ASTNode *node,
  const char *message, sl_MessageType type);

sl_ASTNode *
sl_parse_input(sl_LexerState *input, int *error);

/* --- Verifier --- */
extern int verbose;

int
sl_verify_and_add_file(const char *path, sl_LogicState *logic);

#endif
