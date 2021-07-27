#include "parse.h"
#include "common.h"
#include <string.h>

#define BUFFER_SIZE 16384

struct SymbolToken
{
  const char *string;
  sl_LexerTokenType type;
};

static const struct SymbolToken symbols[] = {
  { "//", sl_LexerTokenType_LineComment },
  { "/*", sl_LexerTokenType_OpeningBlockComment },
  { "*/", sl_LexerTokenType_ClosingBlockComment },
  { "(", sl_LexerTokenType_OpeningParenthesis },
  { ")", sl_LexerTokenType_ClosingParenthesis },
  { "{", sl_LexerTokenType_OpeningBrace },
  { "}", sl_LexerTokenType_ClosingBrace },
  { "<", sl_LexerTokenType_OpeningAngle },
  { ">", sl_LexerTokenType_ClosingAngle },
  { "[", sl_LexerTokenType_OpeningBracket },
  { "]", sl_LexerTokenType_ClosingBracket },
  { "+", sl_LexerTokenType_Plus },
  { ".", sl_LexerTokenType_Dot },
  { ",", sl_LexerTokenType_Comma },
  { ";", sl_LexerTokenType_Semicolon },
  { ":", sl_LexerTokenType_Colon },
  { "%", sl_LexerTokenType_Percent },
  { "$", sl_LexerTokenType_DollarSign }
};

struct sl_LexerState
{
  sl_TextInput *input;

  char *buffer;
  char *overflow_buffer;
  char *read_buffer; /* Points to either buffer, overflow_buffer, or NULL,
                        depending on the length of the line fetched. */
  size_t line_number;
  size_t cursor_offset;

  sl_LexerTokenType token_type;
  char *token_begin;
  size_t token_length;
};

#define CURRENT_CHAR(state) ((state)->read_buffer[(state)->cursor_offset])
#define CURRENT_PTR(state) (&(state)->read_buffer[(state)->cursor_offset])

sl_LexerState *
sl_lexer_new_state_with_input(sl_TextInput *input)
{
  if (input == NULL)
    return NULL;
  sl_LexerState *state = SL_NEW(sl_LexerState);
  if (state == NULL)
    return NULL;
  state->input = input;
  state->buffer = malloc(BUFFER_SIZE);
  if (state->buffer == NULL)
  {
    free(state);
    return NULL;
  }
  state->buffer[0] = '\0';
  state->overflow_buffer = NULL;
  state->read_buffer = NULL;
  state->line_number = 0;
  state->cursor_offset = 0;
  state->token_type = sl_LexerTokenType_None;
  state->token_begin = NULL;
  state->token_length = 0;
  return state;
}

void
sl_lexer_free_state(sl_LexerState *state)
{
  if (state == NULL)
    return;
  if (state->buffer != NULL)
    free(state->buffer);
  if (state->overflow_buffer != NULL)
    free(state->overflow_buffer);
  free(state);
}

static int
fetch_next_line(sl_LexerState *state)
{
  char *result;
  if (state->overflow_buffer != NULL)
    free(state->overflow_buffer);
  if (sl_input_at_end(state->input))
  {
    state->read_buffer = NULL;
    return 0;
  }
  result = sl_input_gets(state->buffer, BUFFER_SIZE, state->input);
  state->cursor_offset = 0;
  if (result == NULL)
  {
    state->read_buffer = NULL;
    return 1;
  }

  /* If the result doesn't end in a newline, copy this into the overflow
     buffer and keep consuming until we get to a newline. */
  if (state->buffer[strlen(state->buffer) - 1] != '\n')
  {
    state->overflow_buffer = strdup(state->buffer);
    if (state->overflow_buffer == NULL)
    {
      state->read_buffer = NULL;
      return 1;
    }
    do {
      char *reallocated;
      result = sl_input_gets(state->buffer, BUFFER_SIZE, state->input);
      if (result == NULL)
      {
        free(state->overflow_buffer);
        state->read_buffer = NULL;
        return 1;
      }
      reallocated = realloc(state->overflow_buffer,
        strlen(state->buffer) + strlen(state->overflow_buffer) + 1);
      if (reallocated == NULL)
      {
        free(state->overflow_buffer);
        state->read_buffer = NULL;
        return 1;
      }
      state->overflow_buffer = reallocated;
      strcat(state->overflow_buffer, state->buffer);
    } while (state->overflow_buffer[strlen(state->overflow_buffer) - 1]
      != '\n');
    state->read_buffer = state->overflow_buffer;
  }
  else
  {
    state->read_buffer = state->buffer;
  }
  ++state->line_number;
  return 0;
}

static bool
is_space_non_newline(char c)
{
  if (isspace(c) && c != '\n')
    return TRUE;
  return FALSE;
}

int
sl_lexer_advance(sl_LexerState *state)
{
  /* If we're at the end of the file, return 1. */
  if (sl_input_at_end(state->input) != 0)
    return 1;
  if (state->read_buffer == NULL)
  {
    int err = fetch_next_line(state);
    if (err)
      return 1;
    else
      state->line_number = 0;
  }
  if (CURRENT_CHAR(state) == '\0')
  {
    int err = fetch_next_line(state);
    if (err)
      return 1;
  }
  if (state->read_buffer == NULL)
    return 1;

  /* Advance until we reach a non-space. */
  while (is_space_non_newline(CURRENT_CHAR(state)))
    ++state->cursor_offset;

  if (CURRENT_CHAR(state) == '\n')
  {
    state->token_type = sl_LexerTokenType_LineEnd;
    state->token_begin = CURRENT_PTR(state);
    state->token_length = 1;
    ++state->cursor_offset;
  }
  else if (isalpha(CURRENT_CHAR(state)) || CURRENT_CHAR(state) == '_')
  {
    /* Parse an identifier. */
    state->token_type = sl_LexerTokenType_Identifier;
    state->token_begin = CURRENT_PTR(state);
    while (isalnum(CURRENT_CHAR(state)) || CURRENT_CHAR(state) == '_')
      ++state->cursor_offset;
    state->token_length = CURRENT_PTR(state) - state->token_begin;
  }
  else if (isdigit(CURRENT_CHAR(state)))
  {
    /* Parse a number. */
    state->token_type = sl_LexerTokenType_Number;
    state->token_begin = CURRENT_PTR(state);
    while (isdigit(CURRENT_CHAR(state)))
      ++state->cursor_offset;
    state->token_length = CURRENT_PTR(state) - state->token_begin;
  }
  else if (CURRENT_CHAR(state) == '"')
  {
    /* Parse a string. */
    bool escaped = FALSE;
    state->token_type = sl_LexerTokenType_String;
    state->token_begin = CURRENT_PTR(state);
    ++state->cursor_offset;
    while (CURRENT_CHAR(state) != '"' || escaped)
    {
      if (CURRENT_CHAR(state) == '\\')
        escaped = TRUE;
      else
        escaped = FALSE;
      ++state->cursor_offset;
    }
    ++state->cursor_offset;
    state->token_length = CURRENT_PTR(state) - state->token_begin;
  }
  else
  {
    /* Parse a symbol. */
    state->token_type = sl_LexerTokenType_Unknown;
    state->token_begin = CURRENT_PTR(state);
    state->token_length = 1;
    for (size_t i = 0; i < sizeof(symbols) / sizeof(struct SymbolToken); ++i)
    {
      if (strncmp(symbols[i].string, CURRENT_PTR(state),
        strlen(symbols[i].string)) == 0)
      {
        state->token_type = symbols[i].type;
        state->token_length = strlen(symbols[i].string);
        break;
      }
    }
    state->cursor_offset += state->token_length;
  }

  return 0;
}


sl_LexerTokenType
sl_lexer_get_current_token_type(const sl_LexerState *state)
{
  if (state == NULL)
    return sl_LexerTokenType_None;
  return state->token_type;
}

struct sl_StringSlice
sl_lexer_get_current_token_string_value(const sl_LexerState *state)
{
  struct sl_StringSlice slice = {};
  if (state == NULL)
    return slice;
  if (state->token_type == sl_LexerTokenType_String)
  {
    /* Cut out the quotes. */
    slice.begin = state->token_begin + 1;
    slice.length = state->token_length - 2;
  }
  else if (state->token_type == sl_LexerTokenType_Identifier)
  {
    slice.begin = state->token_begin;
    slice.length = state->token_length;
  }
  return slice;
}

struct sl_LexerNumber
sl_lexer_get_current_token_numerical_value(const sl_LexerState *state)
{
  struct sl_LexerNumber number;
  number.is_number = FALSE;
  number.value = 0;
  if (state == NULL)
    return number;
  if (state->token_type == sl_LexerTokenType_Number)
  {
    char buffer[64];
    char *overflow;
    number.is_number = TRUE;
    if (state->token_length > 63)
    {
      overflow = strndup(state->token_begin, state->token_length);
      if (overflow == NULL)
      {
        number.is_number = FALSE;
        return number;
      }
      number.value = atoi(overflow);
      free(overflow);
    }
    else
    {
      strncpy(buffer, state->token_begin, state->token_length);
      buffer[state->token_length] = '\0';
      number.value = atoi(buffer);
    }
  }
  return number;
}

uint32_t
sl_lexer_get_current_token_line(const sl_LexerState *state)
{
  return state->line_number;
}

uint32_t
sl_lexer_get_current_token_column(const sl_LexerState *state)
{
  return state->cursor_offset - state->token_length;
}

struct sl_StringSlice
sl_lexer_get_current_token_source(const sl_LexerState *state)
{
  struct sl_StringSlice slice;
  slice.begin = NULL;
  slice.length = 0;
  if (state != NULL)
  {
    slice.begin = state->token_begin;
    slice.length = state->token_length;
  }
  return slice;
}

int
sl_lexer_clear_unused(sl_LexerState *state)
{
  /* Clear away line endings and comments. */
  bool in_line_comment;
  int block_comment_depth;

  in_line_comment = FALSE;
  block_comment_depth = 0;

  do {
    if (sl_lexer_get_current_token_type(state) == sl_LexerTokenType_LineEnd)
    {
      in_line_comment = FALSE;
    }
    else if (sl_lexer_get_current_token_type(state)
      == sl_LexerTokenType_LineComment)
    {
      in_line_comment = TRUE;
    }
    else if (sl_lexer_get_current_token_type(state)
      == sl_LexerTokenType_OpeningBlockComment)
    {
      ++block_comment_depth;
    }
    else if (sl_lexer_get_current_token_type(state)
      == sl_LexerTokenType_ClosingBlockComment)
    {
      --block_comment_depth;
    }
    else if (!in_line_comment && block_comment_depth <= 0)
    {
      return 0;
    }

    if (block_comment_depth < 0)
      return 1;
  } while (sl_lexer_advance(state) == 0);
  return 1;
}
