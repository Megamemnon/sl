#include "asm.h"
#include <lex.h>
#include <parse.h>
#include <string.h>
#include <ctype.h>

const char *asm_keywords[] = {
  NULL
};

const char *asm_symbols[] = {
  "@",
  "(", ")",
  "{", "}",
  "[", "]",
  ",", ":", ";",
  "'", "\"",
  "/*", "*/",
  "//",
  NULL
};

enum NodeType
{
  NodeTypeUnidentified = 0,
  NodeTypeProgram,
  NodeTypeDirective,
  NodeTypeArgument,
  NodeTypeNumericLiteral,
  NodeTypeCharacterLiteral,
  NodeTypeStringLiteral,
  NodeTypeConstant,
  NodeTypeList,
  NodeTypeCodeBlock,
  NodeTypeInstruction
};

/* Parser Methods */
struct NodeData
{
  const struct Token *location;

  enum NodeType type;
  char *name;
  union {
    uint64_t numeric;
    char character;
    char *string;
  } value;
};

void
free_node(struct ASTNode *node)
{
  struct NodeData *data = (struct NodeData *)node->data;
  free(data->name);
  free(data);
}

void
copy_node(struct ASTNode *dst, const struct ASTNode *src)
{
  struct NodeData *dst_data = malloc(sizeof(struct NodeData));
  memset(dst_data, 0, sizeof(struct NodeData));

  const struct NodeData *src_data =
    (const struct NodeData *)src->data;
  dst_data->type = src_data->type;
  dst_data->name = strdup(src_data->name);

  dst->data = dst_data;
}

void
init_node(struct ASTNode *node)
{
  node->data = malloc(sizeof(struct NodeData));
  memset(node->data, 0, sizeof(struct NodeData));
  node->free_callback = &free_node;
  node->copy_callback = &copy_node;
}

struct NodeData *
get_node_data(struct ASTNode *node)
{
  return (struct NodeData *)node->data;
}

const struct NodeData *
get_node_data_c(const struct ASTNode *node)
{
  return (const struct NodeData *)node->data;
}

/* TODO: prevent the parser from looping in some scenarios. */
static int
parse_value(struct ParserState *state);

static bool
is_decimal_string(const char *str)
{
  for (const char *c = str; *c != '\0'; ++c)
  {
    if (!isdigit(*c))
      return FALSE;
  }
  return TRUE;
}

static bool
is_hex_string(const char *str)
{
  for (const char *c = str; *c != '\0'; ++c)
  {
    if (!isxdigit(*c))
      return FALSE;
  }
  return TRUE;
}

static int
parse_numeric_literal(struct ParserState *state)
{
  /* Determine if the number is represented in decimal or hexadecimal, and
     parse it accordingly. */
  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->location = get_current_token(state);
  get_node_data(state->ast_current)->type = NodeTypeNumericLiteral;

  if (strlen(get_current_token(state)->value) >= 2 &&
      strncmp(get_current_token(state)->value, "0x", 2) == 0)
  {
    const char *hex_str = &get_current_token(state)->value[2];
    if (!is_hex_string(hex_str))
    {
      add_error(state->unit, get_current_token(state),
        "Number is not a valid hex string.");
      return 1;
    }
    get_node_data(state->ast_current)->value.numeric =
      strtoll(hex_str, NULL, 16);
  }
  else
  {
    if (!is_decimal_string(get_current_token(state)->value))
    {
      add_error(state->unit, get_current_token(state),
        "Number is not a valid decimal string.");
      return 1;
    }
    get_node_data(state->ast_current)->value.numeric =
      strtoll(get_current_token(state)->value, NULL, 10);
  }

  advance(state);
  ascend(state);
  return 0;
}

static int
extract_character_literal(char *dst, const char *literal)
{
  if (strlen(literal) == 1)
  {
    *dst = *literal;
    return 0;
  }
  else if (strlen(literal) == 2 && literal[0] == '\\')
  {
    char escaped_char = literal[1];
    switch(escaped_char)
    {
      case 'n':
        *dst = '\n';
        return 0;
        break;
      case 't':
        *dst = '\t';
        return 0;
        break;
      case '\\':
        *dst = '\\';
        return 0;
        break;
      case '\'':
        *dst = '\'';
        return 0;
        break;
      default:
        return 1;
        break;
    }
  }

  return 1;
}

static int
parse_string_literal(struct ParserState *state)
{
  /* Determine if the literal is for a string or a character. */
  const char *str = get_current_token(state)->value;

  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->location = get_current_token(state);

  if (strlen(str) < 2)
  {
    add_error(state->unit, get_current_token(state),
      "String and character literals need delimiters.");
    return 1;
  }

  if (str[0] == '"')
  {
    get_node_data(state->ast_current)->type = NodeTypeStringLiteral;
    if (str[strlen(str) - 1] != '"')
    {
      add_error(state->unit, get_current_token(state),
        "String literal delimiters do not match.");
    }
    get_node_data(state->ast_current)->value.string =
      malloc(sizeof(char) * (strlen(str) - 2));
    strncpy(get_node_data(state->ast_current)->value.string,
      &str[1], sizeof(char) * (strlen(str) - 2));
  }
  else if (str[0] == '\'')
  {
    get_node_data(state->ast_current)->type = NodeTypeCharacterLiteral;
    if (str[strlen(str) - 1] != '\'')
    {
      add_error(state->unit, get_current_token(state),
        "Character literal delimiters do not match.");
    }
    char *char_literal = malloc(sizeof(char) * (strlen(str) - 2));
    strncpy(char_literal, &str[1], sizeof(char) * (strlen(str) - 2));
    int err = extract_character_literal(
      &get_node_data(state->ast_current)->value.character, char_literal);
    free(char_literal);
    if (err)
    {
      add_error(state->unit, get_current_token(state),
        "Unknown character literal");
      return 1;
    }
  }
  else
  {
    add_error(state->unit, get_current_token(state),
      "Unknown string literal type. Use single or double quotes.");
    return 1;
  }

  advance(state);
  ascend(state);
  return 0;
}

static int
parse_list(struct ParserState *state)
{
  int err = 0;

  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->location = get_current_token(state);
  get_node_data(state->ast_current)->type = NodeTypeList;

  /* Lists must begin with '['. */
  if (!consume_symbol(state, "["))
  {
    add_error(state->unit, get_current_token(state),
      "Lists must begin with '['.");
    err = 1;
  }

  /* Add items until the list ends. */
  bool first_token = TRUE;
  while (!consume_symbol(state, "]"))
  {
    /* Expect comma-separation between arguments. */
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "Expected a ',' between list items.");
        err = 1;
      }
    }
    if (first_token)
      first_token = FALSE;

    /* Parse the value. */
    err |= parse_value(state);
  }

  ascend(state);
  return err;
}

static int
parse_instruction(struct ParserState *state)
{
  int err = 0;

  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->location = get_current_token(state);
  get_node_data(state->ast_current)->type = NodeTypeInstruction;

  /* Get the name of the instruction. */
  const char *instruction_name;
  if (!consume_identifier(state, &instruction_name))
  {
    add_error(state->unit, get_current_token(state),
      "Expected a name for the instruction.");
    err = 1;
  }
  else
  {
    get_node_data(state->ast_current)->name = strdup(instruction_name);
  }

  /* Parse the arguments. */
  bool first_token = TRUE;
  while (!consume_symbol(state, ";"))
  {
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "Expected a ',' between instruction arguments.");
        err = 1;
      }
    }
    if (first_token)
      first_token = FALSE;

    parse_value(state);
  }

  ascend(state);
  return err;
}

static int
parse_code_block(struct ParserState *state)
{
  int err = 0;

  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->location = get_current_token(state);
  get_node_data(state->ast_current)->type = NodeTypeCodeBlock;

  /* Code blocks must always start with '{'. */
  if (!consume_symbol(state, "{"))
  {
    add_error(state->unit, get_current_token(state),
      "Code blocks must begin with '{'.");
    err = 1;
  }

  while (!consume_symbol(state, "}"))
  {
    err |= parse_instruction(state);
  }

  ascend(state);
  return err;
}

static int
parse_argument_list(struct ParserState *state)
{
  /* Argument lists must start with '('. */
  if (!consume_symbol(state, "("))
  {
    add_error(state->unit, get_current_token(state),
      "Expected an argument list, which must begin with '('.");
  }

  /* Add arguments until the list ends. */
  bool first_token = TRUE;
  while (!consume_symbol(state, ")"))
  {
    /* Expect comma-separation between arguments. */
    if (!first_token)
    {
      if (!consume_symbol(state, ","))
      {
        add_error(state->unit, get_current_token(state),
          "Expected a ',' between arguments.");
      }
    }
    if (first_token)
      first_token = FALSE;

    add_child_and_descend(state);
    init_node(state->ast_current);
    get_node_data(state->ast_current)->type = NodeTypeArgument;
    get_node_data(state->ast_current)->location = get_current_token(state);

    /* Each argument must begin with a name. */
    const char *argument_name;
    if (!consume_identifier(state, &argument_name))
    {
      add_error(state->unit, get_current_token(state),
        "Expected a name for the argument.");
    }
    else
    {
      get_node_data(state->ast_current)->name = strdup(argument_name);
    }

    /* Between the name and the value of an argument, expect a ':'. */
    if (!consume_symbol(state, ":"))
    {
      add_error(state->unit, get_current_token(state),
        "Expected a ':' between the argument name and value.");
    }

    /* Parse the value passed by this argument. */
    int err = parse_value(state);
    PROPAGATE_ERROR(err);

    ascend(state);
  }

  return 0;
}

static int
parse_directive(struct ParserState *state)
{
  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->type = NodeTypeDirective;
  get_node_data(state->ast_current)->location = get_current_token(state);

  /* Directives must start with '@'. */
  if (!consume_symbol(state, "@"))
  {
    add_error(state->unit, get_current_token(state),
      "Expected a directive, which must begin with '@'.");
  }

  /* Directives require a name. */
  const char *directive_name;
  if (!consume_identifier(state, &directive_name))
  {
    add_error(state->unit, get_current_token(state),
      "Expected a name for the directive.");
  }
  else
  {
    get_node_data(state->ast_current)->name = strdup(directive_name);
  }

  /* See if the directive is provided with arguments. */
  if (next_is_symbol(state, "("))
  {
    PROPAGATE_ERROR(parse_argument_list(state));
  }

  ascend(state);
  return 0;
}

static int
parse_constant(struct ParserState *state)
{
  add_child_and_descend(state);
  init_node(state->ast_current);
  get_node_data(state->ast_current)->type = NodeTypeConstant;
  get_node_data(state->ast_current)->location = get_current_token(state);

  /* Constants require a name. */
  const char *constant_name;
  if (!consume_identifier(state, &constant_name))
  {
    add_error(state->unit, get_current_token(state),
      "Expected a name for the constant.");
  }
  else
  {
    get_node_data(state->ast_current)->name = strdup(constant_name);
  }

  ascend(state);
  return 0;
}

static int
parse_value(struct ParserState *state)
{
  int err = 0;

  const struct Token *tok = get_current_token(state);
  if (tok->type == TokenTypeNumericLiteral)
  {
    err |= parse_numeric_literal(state);
  }
  else if (tok->type == TokenTypeStringLiteral)
  {
    err |= parse_string_literal(state);
  }
  else if (next_is_symbol(state, "{"))
  {
    err |= parse_code_block(state);
  }
  else if (next_is_symbol(state, "["))
  {
    err |= parse_list(state);
  }
  else if (next_is_symbol(state, "@"))
  {
    err |= parse_directive(state);
  }
  else
  {
    err |= parse_constant(state);
  }

  return err;
}

static int
parse_program(struct ParserState *state)
{
  int err = 0;

  init_tree(&state->ast_root);

  init_node(state->ast_current);
  get_node_data(state->ast_current)->type = NodeTypeProgram;

  while (!done_parsing(state))
  {
    err |= parse_directive(state);
    PROPAGATE_ERROR(err);
  }

  return err;
}

/* TODO: actually implement it. */
static char *
get_escaped_char(char c)
{
  char *str = malloc(sizeof(char) * 2);
  str[0] = c;
  str[1] = '\0';
  return str;
}

static void
print_node(char *buf, size_t len, const struct ASTNode *node)
{
  const struct NodeData *data = get_node_data_c(node);
  switch (data->type)
  {
    case NodeTypeProgram:
      snprintf(buf, len, "Program");
      break;
    case NodeTypeDirective:
      snprintf(buf, len, "Directive<%s>", data->name);
      break;
    case NodeTypeArgument:
      snprintf(buf, len, "Argument<%s>", data->name);
      break;
    case NodeTypeNumericLiteral:
      snprintf(buf, len, "Numeric Literal<%llu>", data->value.numeric);
      break;
    case NodeTypeStringLiteral:
      snprintf(buf, len, "String Literal<\"%s\">", data->value.string);
      break;
    case NodeTypeCharacterLiteral:
      {
        char *char_str = get_escaped_char(data->value.character);
        snprintf(buf, len, "Character Literal<'%s'>", char_str);
        free(char_str);
      }
      break;
    case NodeTypeConstant:
      snprintf(buf, len, "Constant<%s>", data->name);
      break;
    case NodeTypeList:
      snprintf(buf, len, "List");
      break;
    case NodeTypeCodeBlock:
      snprintf(buf, len, "Code Block");
      break;
    case NodeTypeInstruction:
      snprintf(buf, len, "Instruction<%s>", data->name);
      break;
    default:
      snprintf(buf, len, "Unknown");
      break;
  }
}

struct CodegenState
{
  struct CompilationUnit *unit;
  const struct ParserState *input;
  FILE *out;
};

int
assemble(const char *input_path, FILE *out)
{
  /* Open the file. */
  struct CompilationUnit unit = {};
  open_compilation_unit(&unit, input_path);

  /* Lex the file */
  struct LexState lex_out = {};
  init_lex_state(&lex_out);
  file_to_lines(&lex_out, &unit);
  tokenize_strings(&lex_out, '\'');
  tokenize_strings(&lex_out, '"');
  remove_whitespace(&lex_out);
  separate_symbols(&lex_out);
  tokenize_numeric_literals(&lex_out);
  identify_symbols(&lex_out, asm_symbols);
  remove_block_comments(&lex_out, "/*", "*/");
  remove_line_comments(&lex_out, "//");
  separate_identifiers(&lex_out);
  identify_keywords(&lex_out, asm_keywords);
  remove_line_ends(&lex_out);

  /* Parse the file */
  struct ParserState parse_out = {};
  parse_out.unit = &unit;
  parse_out.input = &lex_out;
  parse_out.ast_current = &parse_out.ast_root;

  int err = parse_program(&parse_out);
  if (err)
  {
    /* TODO: handle error and clean up (maybe continue if not fatal?). */
    print_errors(&unit);
  }

  print_tree(&parse_out.ast_root, &print_node);

  /* Generate machine code. */

  /* Clean up */
  free_tree(&parse_out.ast_root);
  free_lex_state(&lex_out);
  close_compilation_unit(&unit);

  return 0;
}
