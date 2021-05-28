#include "lex.h"
#include "common.h"

#include <stdio.h>
#include <string.h>
#include <ctype.h>

const char *token_type_names[] = {
  "Intermediate",
  "Keyword",
  "Identifier",
  "Symbol",
  "String Literal",
  "Numeric Literal",
  "Line End"
};

static int
is_extended_alnum(char c)
{
  return isalnum(c) || (c == '_');
}

void
snprint_token(char *s, size_t n, const struct Token *tok)
{
  if (tok->value != NULL)
    snprintf(s, n, "Token<%s : \"%s\">", token_type_names[tok->type], tok->value);
  else
    snprintf(s, n, "Token<%s>", token_type_names[tok->type]);
}

struct Token
duplicate_token(const struct Token *src)
{
  struct Token tok = *src;
  if (src->value != NULL)
    tok.value = strdup(src->value);
  return tok;
}

void
copy_lex_result(struct LexResult *dst, const struct LexResult *src)
{
  /* Copy the array of tokens, then duplicate the string contents. */
  free_lex_result(dst);
  ARRAY_COPY(dst->tokens, dst->tokens_n, src->tokens, src->tokens_n);
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].value != NULL)
      dst->tokens[i].value = strdup(src->tokens[i].value);
  }
}

void
free_lex_result(struct LexResult *result)
{
  for (size_t i = 0; i < result->tokens_n; ++i)
  {
    if (result->tokens[i].value != NULL)
      free(result->tokens[i].value);
  }
  if (result->tokens != NULL)
    ARRAY_FREE(result->tokens, result->tokens_n);
}

void
file_to_lines(struct LexResult *dst, const char *file_path)
{
  free_lex_result(dst);
  ARRAY_INIT(dst->tokens, dst->tokens_n);

  if (verbose >= 1)
    printf("Parsing file '%s'\n", file_path);

  FILE *file = fopen(file_path, "r");

  if (file == NULL)
  {
    printf("Could not open file '%s'\n", file_path);
    return;
  }

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeIntermediate;

  char line_buf[4096];
  size_t line = 0;
  while (fgets(line_buf, 4096, file) != NULL)
  {
    tok.value = strdup(line_buf);
    tok.line = line;
    tok.char_offset = 0;
    ARRAY_APPEND(tok, dst->tokens, dst->tokens_n);
    ++line;
  }

  fclose(file);
}

void
remove_whitespace(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  struct Token tok = {};
  tok.id = 0;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeIntermediate)
    {
      const char *token_start = NULL;
      for (const char *c = src->tokens[i].value; ; ++c)
      {
        if (token_start == NULL && !isspace(*c))
          token_start = c;

        if (token_start != NULL && isspace(*c))
        {
          /* Add the token */
          size_t length = c - token_start;
          tok.type = TokenTypeIntermediate;
          tok.value = malloc(sizeof(char) * (length + 1));
          strncpy(tok.value, token_start, length);
          tok.value[length] = '\0';
          ARRAY_APPEND(tok, result.tokens, result.tokens_n);

          token_start = NULL;
        }

        if (*c == '\n')
        {
          /* Add the token */
          tok.type = TokenTypeLineEnd;
          tok.value = NULL;
          ARRAY_APPEND(tok, result.tokens, result.tokens_n);
        }

        if (*c == '\0')
          break;
      }
    }
    else
    {
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
    }
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
separate_symbols(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeIntermediate;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeIntermediate)
    {
      const char *token_start = src->tokens[i].value;
      int in_symbol = !is_extended_alnum(*token_start);
      if (in_symbol)
        tok.type = TokenTypeSymbol;
      else
        tok.type = TokenTypeIntermediate;
      for (const char *c = src->tokens[i].value; ; ++c)
      {
        if ((!in_symbol && !is_extended_alnum(*c))
            || (in_symbol && is_extended_alnum(*c))
            || (*c == '\0'))
        {
          /* Add the token */
          if (in_symbol)
            tok.type = TokenTypeSymbol;
          else
            tok.type = TokenTypeIntermediate;
          size_t length = c - token_start;
          tok.value = malloc(sizeof(char) * (length + 1));
          strncpy(tok.value, token_start, length);
          tok.value[length] = '\0';
          ARRAY_APPEND(tok, result.tokens, result.tokens_n);

          token_start = c;
        }
        in_symbol = !is_extended_alnum(*c);

        if (*c == '\0')
          break;
      }
    }
    else
    {
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
    }
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
identify_symbol(struct LexResult *dst, const struct LexResult *src,
  const char *symbol)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  struct Token tok;
  tok.id = 0;
  tok.type = TokenTypeSymbol;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeSymbol &&
        !src->tokens[i].identified)
    {
      /* Scan the token for the symbol as a substring, and cut it out if
         it exists. */
      const char *symbol_start = src->tokens[i].value;
      const char *c = src->tokens[i].value;
      while (1)
      {
        if (strncmp(c, symbol, strlen(symbol)) == 0)
        {
          size_t prev_length = c - symbol_start;
          if (prev_length > 0)
          {
            tok.value = malloc(sizeof(char) * (prev_length + 1));
            strncpy(tok.value, symbol_start, prev_length);
            tok.value[prev_length] = '\0';
            tok.identified = 0;
            ARRAY_APPEND(tok, result.tokens, result.tokens_n);
          }

          tok.value = strdup(symbol);
          tok.identified = 1;
          ARRAY_APPEND(tok, result.tokens, result.tokens_n);

          c += strlen(symbol);
          symbol_start = c;
          continue;
        }
        if (*c == '\0')
        {
          size_t prev_length = c - symbol_start;
          if (prev_length > 0)
          {
            tok.value = malloc(sizeof(char) * (prev_length + 1));
            strncpy(tok.value, symbol_start, prev_length);
            tok.value[prev_length] = '\0';
            tok.identified = 0;
            ARRAY_APPEND(tok, result.tokens, result.tokens_n);
          }

          break;
        }
        ++c;
      }
    }
    else
    {
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
    }
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
identify_symbols(struct LexResult *dst, const struct LexResult *src,
  const char **symbols)
{
  struct LexResult result = {};
  copy_lex_result(&result, src);

  for (const char **sym = symbols; *sym != NULL; ++sym)
  {
    identify_symbol(&result, &result, *sym);
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
separate_identifiers(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeIdentifier;
  tok.identified = 1;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeIntermediate)
    {
      /* TODO: Don't be dumb here. */
      tok.value = strdup(src->tokens[i].value);
      ARRAY_APPEND(tok, result.tokens, result.tokens_n);
    }
    else
    {
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
    }
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
identify_keyword(struct LexResult *dst, struct LexResult *src,
  const char *keyword)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeKeyword;
  tok.identified = 1;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeIdentifier)
    {
      if (strcmp(src->tokens[i].value, keyword) == 0)
      {
        tok.value = strdup(keyword);
        ARRAY_APPEND(tok, result.tokens, result.tokens_n);
      }
      else
      {
        ARRAY_APPEND(duplicate_token(&src->tokens[i]),
          result.tokens, result.tokens_n);
      }
    }
    else
    {
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
    }
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
identify_keywords(struct LexResult *dst, struct LexResult *src,
  const char **keywords)
{
  struct LexResult result = {};
  copy_lex_result(&result, src);

  for (const char **keyword = keywords; *keyword != NULL; ++keyword)
  {
    identify_keyword(&result, &result, *keyword);
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
remove_line_comments(struct LexResult *dst, const struct LexResult *src,
  const char *line_comment_symbol)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  int in_comment = 0;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeSymbol &&
        strcmp(src->tokens[i].value, line_comment_symbol) == 0)
      in_comment = 1;
    if (src->tokens[i].type == TokenTypeLineEnd)
      in_comment = 0;

    if (!in_comment)
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
remove_block_comments(struct LexResult *dst, const struct LexResult *src,
  const char *block_comment_begin, const char *block_comment_end)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  int in_comment = 0;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type == TokenTypeSymbol &&
        strcmp(src->tokens[i].value, block_comment_begin) == 0)
      in_comment = 1;

    if (!in_comment)
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);

    if (src->tokens[i].type == TokenTypeSymbol &&
        strcmp(src->tokens[i].value, block_comment_end) == 0)
      in_comment = 0;
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}

void
remove_line_ends(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, result.tokens_n);

  int in_comment = 0;
  for (size_t i = 0; i < src->tokens_n; ++i)
  {
    if (src->tokens[i].type != TokenTypeLineEnd)
      ARRAY_APPEND(duplicate_token(&src->tokens[i]),
        result.tokens, result.tokens_n);
  }

  free_lex_result(dst);

  dst->tokens = result.tokens;
  dst->tokens_n = result.tokens_n;
}
