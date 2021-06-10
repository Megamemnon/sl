#include "lex.h"

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
  ARRAY_COPY(dst->tokens, src->tokens);
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    struct Token *dst_tok = ARRAY_GET(dst->tokens, struct Token, i);
    if (src_tok->value != NULL)
      dst_tok->value = strdup(src_tok->value);
  }
}

void
free_lex_result(struct LexResult *result)
{
  for (size_t i = 0; i < ARRAY_LENGTH(result->tokens); ++i)
  {
    struct Token *tok = ARRAY_GET(result->tokens, struct Token, i);
    if (tok->value != NULL)
      free(tok->value);
  }
  if (result->tokens.data != NULL)
    ARRAY_FREE(result->tokens);
}

void
add_error(struct CompilationUnit *unit, const struct Token *location,
  const char *msg)
{
  struct CompilationError err = {
    .location = location,
    .msg = strdup(msg)
  };
  ARRAY_APPEND(unit->errors, struct CompilationError, err);
}

void
print_errors(struct CompilationUnit *unit)
{
  for (size_t i = 0; i < ARRAY_LENGTH(unit->errors); ++i)
  {
    struct CompilationError *err = ARRAY_GET(unit->errors,
      struct CompilationError, i);
    char line_buf[4096];
    size_t line_start = *ARRAY_GET(unit->line_map, size_t, err->location->line);
    fseek(unit->source, line_start, SEEK_SET);
    fgets(line_buf, 4096, unit->source);
    printf("Error '%s' at line '%zu' of file '%s':\n", err->msg,
      err->location->line + 1, unit->source_file);
    printf("%zu  |  %s", err->location->line + 1, line_buf);
  }
}

int
open_compilation_unit(struct CompilationUnit *unit, const char *file_path)
{
  unit->source = fopen(file_path, "r");
  /* TODO: check that this isn't NULL. */

  unit->source_file = strdup(file_path);

  ARRAY_INIT(unit->line_map, size_t);
  ARRAY_INIT(unit->errors, struct CompilationError);

  /* Make a list of the position at which each line starts. */
  char line_buf[4096];
  do
  {
    size_t offset = ftell(unit->source);
    ARRAY_APPEND(unit->line_map, size_t, offset);
  }
  while (fgets(line_buf, 4096, unit->source) != NULL);

  return 0;
}

void
close_compilation_unit(struct CompilationUnit *unit)
{
  fclose(unit->source);
  free(unit->source_file);
  ARRAY_FREE(unit->line_map);
  for (size_t i = 0; i < ARRAY_LENGTH(unit->errors); ++i)
    free(ARRAY_GET(unit->errors, struct CompilationError, i)->msg);
  ARRAY_FREE(unit->errors);
}

void
file_to_lines(struct LexResult *dst, const struct CompilationUnit *unit)
{
  free_lex_result(dst);
  ARRAY_INIT(dst->tokens, struct Token);

  char line_buf[4096];
  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeIntermediate;
  for (size_t i = 0; i < ARRAY_LENGTH(unit->line_map); ++i)
  {
    size_t line_start = *ARRAY_GET(unit->line_map, size_t, i);
    fseek(unit->source, line_start, SEEK_SET);
    fgets(line_buf, 4096, unit->source);
    tok.value = strdup(line_buf);
    tok.line = i;
    tok.char_offset = 0;
    ARRAY_APPEND(dst->tokens, struct Token, tok);
  }
}

void
remove_whitespace(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  struct Token tok = {};
  tok.id = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    if (src_tok->type == TokenTypeIntermediate)
    {
      const char *token_start = NULL;
      tok.line = src_tok->line;
      for (const char *c = src_tok->value; ; ++c)
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
          tok.char_offset = token_start - src_tok->value;
          ARRAY_APPEND(result.tokens, struct Token, tok);

          token_start = NULL;
        }

        if (*c == '\n')
        {
          /* Add the token */
          tok.type = TokenTypeLineEnd;
          tok.value = NULL;
          ARRAY_APPEND(result.tokens, struct Token, tok);
        }

        if (*c == '\0')
          break;
      }
    }
    else
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
}

void
separate_symbols(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeIntermediate;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    tok.line = src_tok->line;
    if (src_tok->type == TokenTypeIntermediate)
    {
      const char *token_start = src_tok->value;
      int in_symbol = !is_extended_alnum(*token_start);
      if (in_symbol)
        tok.type = TokenTypeSymbol;
      else
        tok.type = TokenTypeIntermediate;
      for (const char *c = src_tok->value; ; ++c)
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
          ARRAY_APPEND(result.tokens, struct Token, tok);

          token_start = c;
        }
        in_symbol = !is_extended_alnum(*c);

        if (*c == '\0')
          break;
      }
    }
    else
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
}

void
identify_symbol(struct LexResult *dst, const struct LexResult *src,
  const char *symbol)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  struct Token tok;
  tok.id = 0;
  tok.type = TokenTypeSymbol;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    tok.line = src_tok->line;
    if (src_tok->type == TokenTypeSymbol &&
        !src_tok->identified)
    {
      /* Scan the token for the symbol as a substring, and cut it out if
         it exists. */
      const char *symbol_start = src_tok->value;
      const char *c = src_tok->value;
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
            ARRAY_APPEND(result.tokens, struct Token, tok);
          }

          tok.value = strdup(symbol);
          tok.identified = 1;
          ARRAY_APPEND(result.tokens, struct Token, tok);

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
            ARRAY_APPEND(result.tokens, struct Token, tok);
          }

          break;
        }
        ++c;
      }
    }
    else
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
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
}

void
separate_identifiers(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeIdentifier;
  tok.identified = 1;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    tok.line = src_tok->line;
    if (src_tok->type == TokenTypeIntermediate)
    {
      /* TODO: Don't be dumb here. */
      tok.value = strdup(src_tok->value);
      ARRAY_APPEND(result.tokens, struct Token, tok);
    }
    else
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
}

void
identify_keyword(struct LexResult *dst, struct LexResult *src,
  const char *keyword)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  struct Token tok = {};
  tok.id = 0;
  tok.type = TokenTypeKeyword;
  tok.identified = 1;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    tok.line = src_tok->line;
    if (src_tok->type == TokenTypeIdentifier)
    {
      if (strcmp(src_tok->value, keyword) == 0)
      {
        tok.value = strdup(keyword);
        ARRAY_APPEND(result.tokens, struct Token, tok);
      }
      else
      {
        ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
      }
    }
    else
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
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
}

void
remove_line_comments(struct LexResult *dst, const struct LexResult *src,
  const char *line_comment_symbol)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  int in_comment = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    if (src_tok->type == TokenTypeSymbol &&
        strcmp(src_tok->value, line_comment_symbol) == 0)
      in_comment = 1;
    if (src_tok->type == TokenTypeLineEnd)
      in_comment = 0;

    if (!in_comment)
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
}

void
remove_block_comments(struct LexResult *dst, const struct LexResult *src,
  const char *block_comment_begin, const char *block_comment_end)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  int in_comment = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    if (src_tok->type == TokenTypeSymbol &&
        strcmp(src_tok->value, block_comment_begin) == 0)
      in_comment = 1;

    if (!in_comment)
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }

    if (src_tok->type == TokenTypeSymbol &&
        strcmp(src_tok->value, block_comment_end) == 0)
      in_comment = 0;
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
}

void
remove_line_ends(struct LexResult *dst, const struct LexResult *src)
{
  struct LexResult result = {};
  ARRAY_INIT(result.tokens, struct Token);

  int in_comment = 0;
  for (size_t i = 0; i < ARRAY_LENGTH(src->tokens); ++i)
  {
    const struct Token *src_tok = ARRAY_GET(src->tokens, struct Token, i);
    if (src_tok->type != TokenTypeLineEnd)
    {
      ARRAY_APPEND(result.tokens, struct Token, duplicate_token(src_tok));
    }
  }

  free_lex_result(dst);
  dst->tokens = result.tokens;
}
