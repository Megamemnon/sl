#ifndef LEX_H
#define LEX_H

#include <stdlib.h>

struct LexSpec
{
  const char **keywords;
  size_t keywords_n;

  const char **symbols;
  size_t symbols_n;

  const char **line_comment_symbols;
  size_t line_comment_symbols_n;
};

enum TokenType
{
  TokenTypeKeyword = 0,
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
};

struct LexResult
{
  struct Token *tokens;
  size_t tokens_n;
};

void
snprint_token(char *s, size_t n, const struct Token *tok);

struct LexResult
lex_file(const char *file_path, const struct LexSpec *spec);

void
tokenize_line(const char *line, const struct LexSpec *spec,
  struct LexResult *result);

#endif
