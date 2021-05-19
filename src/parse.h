#ifndef PARSE_H
#define PARSE_H

#include <stdlib.h>

struct ParseSpec
{
  const char **keywords;
  size_t keywords_n;

  const char **symbols;
  size_t symbols_n;
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

struct ParseResult
{

};

void
snprint_token(char *s, size_t n, const struct Token *tok);

struct ParseResult
parse_file(const char *file_path, const struct ParseSpec *spec);

void
tokenize_line(const char *line, const struct ParseSpec *spec,
  struct LexResult *result);

#endif
