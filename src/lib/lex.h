#ifndef LEX_H
#define LEX_H

#include <stdlib.h>
#include <stdio.h>
#include "common.h"

enum TokenType
{
  TokenTypeIntermediate = 0,
  TokenTypeKeyword,
  TokenTypeIdentifier,
  TokenTypeSymbol,
  TokenTypeStringLiteral,
  TokenTypeNumericLiteral,
  TokenTypeLineEnd
};

struct Token
{
  unsigned int id;
  enum TokenType type;
  char *value;
  int identified;

  unsigned int line;
  unsigned int char_offset;
};

void
snprint_token(char *s, size_t n, const struct Token *tok);

struct Token
duplicate_token(const struct Token *src);

void
free_token(struct Token *tok);

struct CompilationError
{
  const struct Token *location;
  char *msg;
  bool is_note;
};

struct CompilationUnit
{
  FILE *source;
  char *source_file;

  Array line_map;
  Array errors;
};

int
open_compilation_unit(struct CompilationUnit *unit, const char *file_path);

void
close_compilation_unit(struct CompilationUnit *unit);

void
add_error(struct CompilationUnit *unit, const struct Token *location,
  const char *msg);

void
add_note(struct CompilationUnit *unit, const struct Token *location,
  const char *msg);

void
print_errors(struct CompilationUnit *unit);

#define LEX_STATE_TOKEN_BUFFERS 2

struct LexState
{
  /* "Double Buffer" the token list. */
  Array token_buffers[LEX_STATE_TOKEN_BUFFERS];
  size_t current_buffer;
};

Array *
lex_state_front_buffer(struct LexState *state);

Array *
lex_state_back_buffer(struct LexState *state);

void
lex_state_clear_back_buffer(struct LexState *state);

void
lex_state_swap_buffers(struct LexState *state);

void
init_lex_state(struct LexState *state);

void
free_lex_state(struct LexState *state);

void
file_to_lines(struct LexState *state, const struct CompilationUnit *unit);

void
tokenize_strings(struct LexState *state, const char *string_delimiter);

void
separate_symbols(struct LexState *state);

void
remove_whitespace(struct LexState *state);

void
identify_symbol(struct LexState *state, const char *symbol);

/* `symbols` must be NULL-terminated. */
void
identify_symbols(struct LexState *state, const char **symbols);

/* TODO: verify symbols, check that all are identified. */

void
separate_identifiers(struct LexState *state);

void
identify_keyword(struct LexState *state, const char *keyword);

void
identify_keywords(struct LexState *state, const char **keywords);

void
remove_line_comments(struct LexState *state, const char *line_comment_symbol);

/* TODO: option for nested comments? Or a separate function? */
void
remove_block_comments(struct LexState *state,
  const char *block_comment_begin, const char *block_comment_end);

void
remove_line_ends(struct LexState *state);

#endif
