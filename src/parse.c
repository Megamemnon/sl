#include "parse.h"
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
is_keyword(const char *str, const struct ParseSpec *spec)
{
  for (size_t i = 0; i < spec->keywords_n; ++i)
  {
    if (strcmp(str, spec->keywords[i]) == 0)
      return 1;
  }
  return 0;
}

static void
remove_comments(struct LexResult *result)
{

}

void
snprint_token(char *s, size_t n, const struct Token *tok)
{
  snprintf(s, n, "Token<%s : \"%s\">", token_type_names[tok->type], tok->value);
}

struct ParseResult
parse_file(const char *file_path,
  const struct ParseSpec *spec)
{
  struct LexResult lex = {};
  struct ParseResult result = {};

  ARRAY_INIT(lex.tokens, lex.tokens_n);

  if (verbose >= 1)
    printf("Parsing file '%s'\n", file_path);

  FILE *file = fopen(file_path, "r");
  if (file == NULL)
  {
    printf("Could not open file '%s'\n", file_path);
    return result;
  }

  char line_buf[4096];
  while (fgets(line_buf, 4096, file) != NULL)
  {
    tokenize_line(line_buf, spec, &lex);
  }

  fclose(file);

  /* TMP: print the tokens */
  char buf[1024];
  for (size_t i = 0; i < lex.tokens_n; ++i)
  {
    snprint_token(buf, 1024, &lex.tokens[i]);
    printf("%s\n", buf);
  }

  ARRAY_FREE(lex.tokens, lex.tokens_n);

  return result;
}

void
tokenize_line(const char *line, const struct ParseSpec *spec,
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
