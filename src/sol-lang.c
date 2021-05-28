#include "sol-lang.h"
#include "parse.h"
#include "common.h"

#include <string.h>

// TODO: remove debug stuff
#include <stdio.h>

const char *sol_keywords[] = {
  "namespace",
  "import",
  "formula",
  "Formula",
  "hypothesis",
  "infer",
  "rule",
  "axiom",
  "theorem",
  "step",
  "Var",
  NULL
};
const char *sol_symbols[] = {
  "(", ")",
  "[", "]",
  "{", "}",
  ".", ",", ";", ":",
  "/*", "*/",
  "//",
  NULL
};

/* TODO: this struct and the functions to manipulate it are probably generic
   enough to go in parse.h and parse.c. */
struct ParserState
{
  struct LexResult *input;
  size_t token_index;

  struct ASTNode ast_root;
  struct ASTNode *ast_current;
};

static struct Token *
get_current_token(struct ParserState *state)
{
  return &state->input->tokens[state->token_index];
}

/* If the current token is the keyword, "consume" it and advance the parser. */
static int
consume_keyword(struct ParserState *state, const char *keyword)
{
  if (get_current_token(state)->type == TokenTypeKeyword
      && strcmp(get_current_token(state)->value, keyword) == 0)
  {
    ++state->token_index;
    return 1;
  }
  return 0;
}

static int
consume_symbol(struct ParserState *state, const char *symbol)
{
  if (get_current_token(state)->type == TokenTypeSymbol
      && strcmp(get_current_token(state)->value, symbol) == 0)
  {
    ++state->token_index;
    return 1;
  }
  return 0;
}

/* If the current token is an identifier, "consume" it and advance. */
static int
consume_identifier(struct ParserState *state, const char **identifier)
{
  if (get_current_token(state)->type == TokenTypeIdentifier)
  {
    *identifier = get_current_token(state)->value;
    ++state->token_index;
    return 1;
  }
  return 0;
}

static void
parse_program(struct ParserState *state);

static void
parse_namespace(struct ParserState *state);

static void
parse_formula(struct ParserState *state);

static void
parse_rule(struct ParserState *state);

static void
parse_theorem(struct ParserState *state);

static void
parse_axiom(struct ParserState *state);

/* Called at the start of parsing. Almost equivalent to
   `parse_namespace`, except no curly braces. */
void
parse_program(struct ParserState *state)
{
  while (state->token_index < state->input->tokens_n)
  {
    {
      char buf[1024];
      snprint_token(buf, 1024, &state->input->tokens[state->token_index]);
      printf("%s\n", buf);
    }

    if (consume_keyword(state, "namespace"))
    {
      struct ASTNode *namespace_node = new_child(state->ast_current);
      parse_namespace(state);
    }
    else if (consume_keyword(state, "rule"))
    {

    }
    else if (consume_keyword(state, "formula"))
    {

    }
    else if (consume_keyword(state, "theorem"))
    {

    }
    else if (consume_keyword(state, "axiom"))
    {

    }
    else
    {
      /* Unrecognized token. */
      break;
    }
  }
}

/* A namespace, which is just a container for other objects:
     - Namespaces
     - Rules
     - Formulas
     - Theorems
     - Axioms */
void
parse_namespace(struct ParserState *state)
{
  /* The next token should be an identifier giving the name of the namespace. */
  const char *namespace_name;
  if (!consume_identifier(state, &namespace_name))
  {
    /* TODO: Error, no name provided. */
  }

  /* Then there should be an opening bracket. */
  if (!consume_symbol(state, "{"))
  {
    /* TODO: Error. */
  }

  /* For now, ignore what's inside and wait until a closing bracket. */
  while (!consume_symbol(state, "}"))
  {
    /* TODO: out of bounds checking! */
    ++state->token_index;
  }

#if 0
  /* Go down the list, looking to create one of these environments. */
  if (consume_keyword(state, "namespace"))
  {
    struct ASTNode *namespace_node = new_child(state->ast_current);
    // parse_namespace(state);
  }
  else if (consume_keyword(state, "rule"))
  {

  }
  else if (consume_keyword(state, "formula"))
  {

  }
  else if (consume_keyword(state, "theorem"))
  {

  }
  else if (consume_keyword(state, "axiom"))
  {

  }
  else
  {
    /* Unrecognized token. */
  }
#endif
}

void
parse_formula(struct ParserState *state)
{

}

void
parse_rule(struct ParserState *state)
{

}

void
parse_theorem(struct ParserState *state)
{

}

void
parse_axiom(struct ParserState *state)
{

}

int
sol_verify(const char *file_path)
{
  /* Lex the file */
  struct LexResult lex_out = {};

  file_to_lines(&lex_out, file_path);
  remove_whitespace(&lex_out, &lex_out);
  separate_symbols(&lex_out, &lex_out);
  identify_symbols(&lex_out, &lex_out, sol_symbols);
  remove_line_comments(&lex_out, &lex_out, "//");
  remove_block_comments(&lex_out, &lex_out, "/*", "*/");
  separate_identifiers(&lex_out, &lex_out);
  identify_keywords(&lex_out, &lex_out, sol_keywords);
  remove_line_ends(&lex_out, &lex_out);

  /* Parse the file */
  struct ParserState parse_out = {};
  parse_out.input = &lex_out;
  parse_out.ast_current = &parse_out.ast_root;
  ARRAY_INIT(parse_out.ast_root.children, parse_out.ast_root.children_n);

  parse_program(&parse_out);

  /* Free the token list. */
  free_lex_result(&lex_out);

  /* TMP: Print the AST to console. */
  print_tree(&parse_out.ast_root);

  /* Free the AST. */
  free_tree(&parse_out.ast_root);

  return 0;
}
