#ifndef PARSE_H
#define PARSE_H

#include "common.h"
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

#include "lex.h"
#include "common.h"
#include <stdlib.h>

/* Generally parsers need to be written per language, so these are just
   general functions for manipulating ASTs. */
struct ASTNode;

typedef void (* free_node_callback_t)(struct ASTNode *);

 /* Copy the user data from the source to the destination. */
typedef void (* copy_node_callback_t)(struct ASTNode *, const struct ASTNode *);

struct ASTNode
{
  struct ASTNode *parent;
  Array children;

  void *data;

  free_node_callback_t free_callback;
  copy_node_callback_t copy_callback;
};

void
init_tree(struct ASTNode *root);

void
free_tree(struct ASTNode *root);

void
copy_tree(struct ASTNode *dst, const struct ASTNode *src);

typedef void (* print_node_callback_t)(char *, size_t, const struct ASTNode *);

void
print_tree(const struct ASTNode *root, print_node_callback_t print_callback);

struct ASTNode *
new_child(struct ASTNode *parent);

typedef void (* traverse_node_callback_t)(const struct ASTNode *, void *);

void
traverse_tree(const struct ASTNode *root, traverse_node_callback_t node_callback,
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

  struct ASTNode ast_root;
  struct ASTNode *ast_current;
};

bool
done_parsing(struct ParserState *state);

Array *
parser_token_buffer(struct ParserState *state);

struct Token *
get_current_token(struct ParserState *state);

void
add_child_and_descend(struct ParserState *state);

void
ascend(struct ParserState *state);

int
advance(struct ParserState *state);

int
consume_keyword(struct ParserState *state, const char *keyword);

bool
next_is_keyword(struct ParserState *state, const char *keyword);

int
consume_symbol(struct ParserState *state, const char *symbol);

bool
next_is_symbol(struct ParserState *state, const char *symbol);

int
consume_identifier(struct ParserState *state, const char **identifier);

bool
next_is_string(struct ParserState *state);

int
consume_string(struct ParserState *state, const char **string);

bool
tokens_remain(struct ParserState *state);

#endif
