#include "lex.h"
#include "common.h"

#include <stdio.h>
#include <string.h>
#include <ctype.h>

const char *token_type_names[] = {
  "Keyword",
  "Identifier",
  "Symbol",
  "String Literal",
  "Numeric Literal",
  "Line End"
};

static int
is_keyword(const char *str, const struct LexSpec *spec)
{
  for (size_t i = 0; i < spec->keywords_n; ++i)
  {
    if (strcmp(str, spec->keywords[i]) == 0)
      return 1;
  }
  return 0;
}

static int
is_line_comment(const struct Token *token, const struct LexSpec *spec)
{
  for (size_t i = 0; i < spec->line_comment_symbols_n; ++i)
  {
    if (token->type == TokenTypeSymbol &&
        strcmp(token->value, spec->line_comment_symbols[i]) == 0)
      return 1;
  }
  return 0;
}

static void
remove_comments(struct LexResult *dst, const struct LexResult *src,
  const struct LexSpec *spec)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  /* First, remove line comments */
  int in_comment = 0;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (is_line_comment(&src->tokens[i], spec))
      in_comment = 1;
    if (src->tokens[i].type == TokenTypeLineEnd)
      in_comment = 0;

    if (!in_comment)
      ARRAY_APPEND(src->tokens[i], result.tokens, result.tokens_n);
  }

  if (dst->tokens != NULL)
    ARRAY_FREE(dst->tokens, dst->tokens_n);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
snprint_token(char *s, size_t n, const struct Token *tok)
{
  snprintf(s, n, "Token<%s : \"%s\">", token_type_names[tok->type], tok->value);
}

struct LexResult
lex_file(const char *file_path,
  const struct LexSpec *spec)
{
  struct LexResult lex = {};

  ARRAY_INIT(lex.tokens, lex.tokens_n);

  if (verbose >= 1)
    printf("Parsing file '%s'\n", file_path);

  FILE *file = fopen(file_path, "r");
  if (file == NULL)
  {
    printf("Could not open file '%s'\n", file_path);
    return lex;
  }

  char line_buf[4096];
  while (fgets(line_buf, 4096, file) != NULL)
  {
    tokenize_line(line_buf, spec, &lex);
  }

  fclose(file);

  remove_comments(&lex, &lex, spec);

  ARRAY_FREE(lex.tokens, lex.tokens_n);

  return lex;
}

void
tokenize_line(const char *line, const struct LexSpec *spec,
  struct LexResult *result)
{
  struct Token tok = {};

  enum ParseMode {
    ParseModeNone = 0,
    ParseModeIdentifier,
    ParseModeNumeric,
    ParseModeString,
    ParseModeSymbol
  };

  enum ParseMode mode = ParseModeNone;
  const char *token_start = NULL;
  for (const char *c = line; *c != '\0'; ++c)
  {
    switch (mode)
    {
      case ParseModeNone:
        break;
      case ParseModeIdentifier:
        if (!isalnum(*c) && *c != '_')
        {
          size_t length = (c - token_start);
          char *token = malloc(sizeof(char) * (length + 1));
          strncpy(token, token_start, length);
          token[length] = '\0';

          if (is_keyword(token, spec))
            tok.type = TokenTypeKeyword;
          else
            tok.type = TokenTypeIdentifier;
          tok.value = token;

          ARRAY_APPEND(tok, result->tokens, result->tokens_n);
          mode = ParseModeNone;
        }
        break;
      case ParseModeNumeric:
        /* Numerics contain alphanumerics + '_', so we end when we encounter
           something else. */
        if (!isalnum(*c) && *c != '_')
        {
          size_t length = (c - token_start);
          char *token = malloc(sizeof(char) * (length + 1));
          strncpy(token, token_start, length);
          token[length] = '\0';

          tok.type = TokenTypeNumericLiteral;
          tok.value = token;

          ARRAY_APPEND(tok, result->tokens, result->tokens_n);
          mode = ParseModeNone;
        }
        break;
      case ParseModeString:
        /* Wait until we have an end quote. */
        if (*c == '"')
        {
          size_t length = (c - token_start) - 1;
          char *token = malloc(sizeof(char) * (length + 1));
          strncpy(token, token_start + 1, length);
          token[length] = '\0';

          tok.type = TokenTypeStringLiteral;
          tok.value = token;

          ARRAY_APPEND(tok, result->tokens, result->tokens_n);
          mode = ParseModeNone;
        }
        break;
      case ParseModeSymbol:
        /* Wait until we encounter and alphanumeric or '_', or whitespace. */
        if (isalnum(*c) || isspace(*c) || *c == '_')
        {
          size_t length = (c - token_start);
          char *token = malloc(sizeof(char) * (length + 1));
          strncpy(token, token_start, length);
          token[length] = '\0';

          tok.type = TokenTypeSymbol;
          tok.value = token;

          ARRAY_APPEND(tok, result->tokens, result->tokens_n);
          mode = ParseModeNone;
        }
        break;
    }

    if (mode == ParseModeNone)
    {
      /* Start a new token, if possible. */
      /* First, check for keywords and identifiers, then literals, then
         symbols. */
      /* Keywords/literals are alphanumeric strings that start with letters
         or an underscore. */
      /* Numeric literals always start with a number, and string literals
         always start with a single or double quote. */
      /* Symbols are anything else that doesn't start with whitespace,
         and end with a space or alphanumeric character. */
      if (isalpha(*c) || *c == '_')
      {
        mode = ParseModeIdentifier;
      }
      else if (isdigit(*c))
      {
        mode = ParseModeNumeric;
      }
      else if (*c == '"')
      {
        mode = ParseModeString;
      }
      else if (!isspace(*c))
      {
        mode = ParseModeSymbol;
      }
      token_start = c;
    }
  }

  tok.type = TokenTypeLineEnd;
  tok.value = "";
  ARRAY_APPEND(tok, result->tokens, result->tokens_n);
}
