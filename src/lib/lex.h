#ifndef LEX_H
#define LEX_H

#include <stdlib.h>
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

struct LexResult
{
  Array tokens;
};

void
snprint_token(char *s, size_t n, const struct Token *tok);

struct Token
duplicate_token(const struct Token *src);

void
copy_lex_result(struct LexResult *dst, const struct LexResult *src);

void
free_lex_result(struct LexResult *result);

void
file_to_lines(struct LexResult *dst, const char *file_path);

void
tokenize_strings(struct LexResult *dst, const struct LexResult *src,
  const char *string_delimiter);

void
separate_symbols(struct LexResult *dst, const struct LexResult *src);

void
remove_whitespace(struct LexResult *dst, const struct LexResult *src);

void
identify_symbol(struct LexResult *dst, const struct LexResult *src,
  const char *symbol);

/* `symbols` must be NULL-terminated. */
void
identify_symbols(struct LexResult *dst, const struct LexResult *src,
  const char **symbols);

/* TODO: verify symbols, check that all are identified. */

void
separate_identifiers(struct LexResult *dst, const struct LexResult *src);

void
identify_keyword(struct LexResult *dst, struct LexResult *src,
  const char *keyword);

void
identify_keywords(struct LexResult *dst, struct LexResult *src,
  const char **keywords);

void
remove_line_comments(struct LexResult *dst, const struct LexResult *src,
  const char *line_comment_symbol);

/* TODO: option for nested comments? Or a separate function? */
void
remove_block_comments(struct LexResult *dst, const struct LexResult *src,
  const char *block_comment_begin, const char *block_comment_end);

void
remove_line_ends(struct LexResult *dst, const struct LexResult *src);

#endif
