#include "test_case.h"
#include <parse.h>
#include <stdio.h>

#define TEST_FILENAME "./tmp_lex_test.txt"

static const char *test_string =
"identifier 1234 // /* */( ) {}< > [ ]\t+\t.\n\t , ; :    %$\n" \
"latex \"this is a string literal!\";\n" \
"latex \"this is a \\\"string literal\\\", \\nbut with escaped \\\'characters\\\'!\";\n" \
"// this is a line comment!\n";

struct TokenValue
{
  sl_LexerTokenType type;
  uint32_t line;
  uint32_t column;
  const char *string_value;
  bool is_number;
  uint32_t number_value;
};

static const struct TokenValue tokens[] = {
  { sl_LexerTokenType_Identifier, 0, 0, "identifier", FALSE, 0 },
  { sl_LexerTokenType_Number, 0, 11, NULL, TRUE, 1234 },
  { sl_LexerTokenType_LineComment, 0, 16, NULL, FALSE, 0 },
  { sl_LexerTokenType_OpeningBlockComment, 0, 19, NULL, FALSE, 0 },
  { sl_LexerTokenType_ClosingBlockComment, 0, 22, NULL, FALSE, 0 },
  { sl_LexerTokenType_OpeningParenthesis, 0, 24, NULL, FALSE, 0 },
  { sl_LexerTokenType_ClosingParenthesis, 0, 26, NULL, FALSE, 0 },
  { sl_LexerTokenType_OpeningBrace, 0, 28, NULL, FALSE, 0 },
  { sl_LexerTokenType_ClosingBrace, 0, 29, NULL, FALSE, 0 },
  { sl_LexerTokenType_OpeningAngle, 0, 30, NULL, FALSE, 0 },
  { sl_LexerTokenType_ClosingAngle, 0, 32, NULL, FALSE, 0 },
  { sl_LexerTokenType_OpeningBracket, 0, 34, NULL, FALSE, 0 },
  { sl_LexerTokenType_ClosingBracket, 0, 36, NULL, FALSE, 0 },
  { sl_LexerTokenType_Plus, 0, 38, NULL, FALSE, 0 },
  { sl_LexerTokenType_Dot, 0, 40, NULL, FALSE, 0 },
  { sl_LexerTokenType_LineEnd, 0, 41, NULL, FALSE, 0 },
  { sl_LexerTokenType_Comma, 1, 2, NULL, FALSE, 0 },
  { sl_LexerTokenType_Semicolon, 1, 4, NULL, FALSE, 0 },
  { sl_LexerTokenType_Colon, 1, 6, NULL, FALSE, 0 },
  { sl_LexerTokenType_Percent, 1, 11, NULL, FALSE, 0 },
  { sl_LexerTokenType_DollarSign, 1, 12, NULL, FALSE, 0 },
  { sl_LexerTokenType_LineEnd, 1, 13, NULL, FALSE, 0 },
  { sl_LexerTokenType_Identifier, 2, 0, "latex", FALSE, 0 },
  { sl_LexerTokenType_String, 2, 6, "this is a string literal!", FALSE, 0 },
  { sl_LexerTokenType_Semicolon, 2, 33, NULL, FALSE, 0 },
  { sl_LexerTokenType_LineEnd, 2, 34, NULL, FALSE, 0 },
  { sl_LexerTokenType_Identifier, 3, 0, "latex", FALSE, 0 },
  { sl_LexerTokenType_String, 3, 6,
    "this is a \"string literal\", \\nbut with escaped \'characters\'!\n",
    FALSE, 0 },
  { sl_LexerTokenType_Semicolon, 3, 72, NULL, FALSE, 0 },
  { sl_LexerTokenType_LineEnd, 3, 73, NULL, FALSE, 0 },
  { sl_LexerTokenType_LineComment, 4, 0, NULL, FALSE, 0 },
  { sl_LexerTokenType_Identifier, 4, 3, "this", FALSE, 0 },
  { sl_LexerTokenType_Identifier, 4, 8, "is", FALSE, 0 },
  { sl_LexerTokenType_Identifier, 4, 11, "a", FALSE, 0 },
  { sl_LexerTokenType_Identifier, 4, 13, "line", FALSE, 0 },
  { sl_LexerTokenType_Identifier, 4, 18, "comment", FALSE, 0 },
  { sl_LexerTokenType_Unknown, 4, 25, NULL, FALSE, 0 },
  { sl_LexerTokenType_LineEnd, 4, 26, NULL, FALSE, 0 },
};

static int
lex_test_string(sl_LexerState *state)
{
  if (state == NULL)
    return 1;

  for (size_t i = 0; i < sizeof(tokens) / sizeof(struct TokenValue); ++i)
  {
    int err = sl_lexer_advance(state);
    if (err != 0)
    {
      printf("Lexer failed to advance %zu.\n", i);
      return 1;
    }
    else if (tokens[i].type != sl_lexer_get_current_token_type(state))
    {
      printf("Token %zu has the wrong type %d (expected %d).\n",
        i, sl_lexer_get_current_token_type(state), tokens[i].type);
      return 1;
    }
    else if (tokens[i].line != sl_lexer_get_current_token_line(state))
    {
      printf("Token %zu has the wrong line number %u (expected %u).\n",
        i, sl_lexer_get_current_token_line(state), tokens[i].line);
      return 1;
    }
    else if (tokens[i].column != sl_lexer_get_current_token_column(state))
    {
      printf("Token %zu has the wrong column %u (expected %u).\n",
        i, sl_lexer_get_current_token_column(state), tokens[i].column);
      return 1;
    }
    else if (tokens[i].string_value == NULL &&
      sl_lexer_get_current_token_string_value(state).begin != NULL)
    {
      printf("Token %zu has the wrong string value %s (expected NULL).\n",
        i, sl_lexer_get_current_token_string_value(state).begin);
      return 1;
    }
    else if (tokens[i].is_number !=
      sl_lexer_get_current_token_numerical_value(state).is_number)
    {
      printf("Token %zu has the wrong numeric type.\n", i);
      return 1;
    }
    else if (tokens[i].number_value !=
      sl_lexer_get_current_token_numerical_value(state).value)
    {
      printf("Token %zu has the wrong numerical value %u (expected %u).\n",
        i, sl_lexer_get_current_token_numerical_value(state).value,
        tokens[i].number_value);
      return 1;
    }
  }

  if (sl_lexer_advance(state) == 0)
  {
    printf("Lexer advanced when it should have reached the end of file.\n");
    return 1;
  }

  return 0;
}

static int
run_test_lexer(struct TestState *state)
{
  /* Write the string to a file in order to test reading from files. */
  sl_LexerState *lex_state;
  int err;
  FILE *f = fopen(TEST_FILENAME, "w");
  fputs(test_string, f);
  fclose(f);

  {
    sl_TextInput *input = sl_input_from_file(TEST_FILENAME);
    lex_state = sl_lexer_new_state_with_input(input);
    err = lex_test_string(lex_state);
    if (err != 0)
      return err;
    sl_lexer_free_state(lex_state);
    sl_input_free(input);
  }

  {
    sl_TextInput *input = sl_input_from_string(test_string);
    lex_state = sl_lexer_new_state_with_input(input);
    err = lex_test_string(lex_state);
    if (err != 0)
      return err;
    sl_lexer_free_state(lex_state);
    sl_input_free(input);
  }

  remove(TEST_FILENAME);
  return 0;
}

struct TestCase test_lexer = { "Lexer", &run_test_lexer };
