#include "parse.h"
#include "common.h"
#include <string.h>

typedef ARR(sl_ASTNode) NodeArray;

struct sl_ASTNode
{
  sl_ASTNode *parent;
  NodeArray children;

  sl_ASTNodeType type;
  size_t line;
  size_t column;
  char *name;
};

int verbose = 0;

const sl_ASTNode *
sl_node_get_parent(const sl_ASTNode *node)
{
  if (node == NULL)
    return NULL;
  return node->parent;
}

size_t
sl_node_get_child_count(const sl_ASTNode *node)
{
  if (node == NULL)
    return 0;
  return ARR_LENGTH(node->children);
}

const sl_ASTNode *
sl_node_get_child(const sl_ASTNode *node, size_t index)
{
  if (node == NULL)
    return NULL;
  if (index >= ARR_LENGTH(node->children))
    return NULL;
  return ARR_GET(node->children, index);
}

sl_ASTNodeType
sl_node_get_type(const sl_ASTNode *node)
{
  if (node == NULL)
    return sl_ASTNodeType_None;
  return node->type;
}

const char *
sl_node_get_name(const sl_ASTNode *node)
{
  if (node == NULL)
    return NULL;
  return node->name;
}

sl_ASTNode *
sl_node_new()
{
  sl_ASTNode *node = SL_NEW(sl_ASTNode);
  node->parent = NULL;
  node->name = NULL;
  ARR_INIT(node->children);
  return node;
}

static void
free_children(sl_ASTNode *root)
{
  for (size_t i = 0; i < ARRAY_LENGTH(root->children); ++i)
  {
    free_children(ARR_GET(root->children, i));
  }
  ARR_FREE(root->children);
  if (root->name != NULL)
    free(root->name);
}

void
sl_node_free(sl_ASTNode *node)
{
  /* Recursively free the children of this node. */
  free_children(node);
}

static void
copy_node_and_children(sl_ASTNode *dst, const sl_ASTNode *src)
{
  ARR_INIT_RESERVE(dst->children, ARR_LENGTH(src->children));
  for (size_t i = 0; i < ARR_LENGTH(src->children); ++i)
  {
    sl_ASTNode *dst_child = ARR_GET(dst->children, i);
    const sl_ASTNode *src_child = ARR_GET(src->children, i);
    copy_node_and_children(dst_child, src_child);
    dst_child->parent = dst;
  }
  {
    dst->type = src->type;
    if (src->name != NULL)
      dst->name = strdup(src->name);
    else
      dst->name = NULL;
  }
}

static void
print_node(char *buf, size_t len, const sl_ASTNode *node)
{
  switch (node->type)
  {
    case sl_ASTNodeType_None:
      snprintf(buf, len, "Unknown<>");
    case sl_ASTNodeType_Namespace:
      if (node->name == NULL)
        snprintf(buf, len, "Namespace<Unnamed>");
      else
        snprintf(buf, len, "Namespace<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Use:
      snprintf(buf, len, "Use<>");
      break;
    case sl_ASTNodeType_Type:
      snprintf(buf, len, "Type<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_AtomicFlag:
      snprintf(buf, len, "Atomic<>");
      break;
    case sl_ASTNodeType_BindsFlag:
      snprintf(buf, len, "Binds<>");
      break;
    case sl_ASTNodeType_Expression:
      snprintf(buf, len, "Expression<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Latex:
      snprintf(buf, len, "Latex<>");
      break;
    case sl_ASTNodeType_Bind:
      snprintf(buf, len, "Bind<>");
      break;
    case sl_ASTNodeType_LatexString:
      snprintf(buf, len, "Latex String<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_LatexVariable:
      snprintf(buf, len, "Latex Variable<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_ConstantDeclaration:
      snprintf(buf, len, "Constant Declaration<>");
      break;
    case sl_ASTNodeType_Axiom:
      snprintf(buf, len, "Axiom<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Theorem:
      snprintf(buf, len, "Theorem<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_ParameterList:
      snprintf(buf, len, "Parameter List<>");
      break;
    case sl_ASTNodeType_Parameter:
      snprintf(buf, len, "Parameter<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Def:
      snprintf(buf, len, "Def<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Assume:
      snprintf(buf, len, "Assume<>");
      break;
    case sl_ASTNodeType_Require:
      snprintf(buf, len, "Require<>");
      break;
    case sl_ASTNodeType_Infer:
      snprintf(buf, len, "Infer<>");
      break;
    case sl_ASTNodeType_Step:
      snprintf(buf, len, "Step<>");
      break;
    case sl_ASTNodeType_Composition:
      snprintf(buf, len, "Composition<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Constant:
      snprintf(buf, len, "Constant<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Variable:
      snprintf(buf, len, "Variable<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_Placeholder:
      snprintf(buf, len, "Placeholder<\"%s\">", node->name);
      break;
    case sl_ASTNodeType_ArgumentList:
      snprintf(buf, len, "Argument List<>");
      break;
    case sl_ASTNodeType_TheoremReference:
      snprintf(buf, len, "Theorem Reference<>");
      break;
    case sl_ASTNodeType_Path:
      snprintf(buf, len, "Path<>");
      break;
    case sl_ASTNodeType_PathSegment:
      snprintf(buf, len, "Path Segment<\"%s\">", node->name);
      break;
    default:
      snprintf(buf, len, "");
      break;
  }
}

static void
print_children(const sl_ASTNode *root, unsigned int depth)
{
  for (size_t i = 0; i < depth; ++i)
    printf(" ");
  char buf[1024];
  print_node(buf, 1024, root);
  printf("%s\n", buf);
  for (size_t i = 0; i < ARR_LENGTH(root->children); ++i)
  {
    print_children(ARR_GET(root->children, i), depth + 1);
  }
}

void
sl_print_tree(const sl_ASTNode *root)
{
  print_children(root, 0);
}

void
sl_node_show_message(sl_TextInput *input, const sl_ASTNode *node,
  const char *message, sl_MessageType type)
{
  sl_input_show_message(input, node->line, node->column, message, type);
}

static sl_ASTNode *
new_child(sl_ASTNode *parent)
{
  sl_ASTNode child = {};
  child.parent = parent;
  ARR_INIT(child.children);

  ARR_APPEND(parent->children, child);

  return ARR_GET(parent->children, ARR_LENGTH(parent->children) - 1);
}

/* --- New Parser --- */
struct _ParserState;

/* Return nonzero to indicate an error. */
union _ParserStepUserData
{
  const char *user_str;
  sl_LexerTokenType token_type;
  sl_ASTNodeType node_type;
  int number;
};

typedef int (* parser_step_exec_t)(struct _ParserState *,
  union _ParserStepUserData);

struct _ParserStep
{
  parser_step_exec_t exec;
  union _ParserStepUserData user_data;
};

struct _ParserState
{
  sl_LexerState *input;
  sl_ASTNode *tree;
  sl_ASTNode *current;

  ARR(struct _ParserStep) stack;
};

static void
_tmp_debug_lex(const sl_LexerState *state)
{
  char *str = slice_to_string(sl_lexer_get_current_token_source(state));
  if (str == NULL)
    return;
  printf("%s\n", str);
  free(str);
}

static union _ParserStepUserData
_user_data_str(const char *str)
{
  union _ParserStepUserData data;
  data.user_str = str;
  return data;
}

static union _ParserStepUserData
_user_data_none()
{
  return _user_data_str(NULL);
}

static union _ParserStepUserData
_user_data_token_type(sl_LexerTokenType type)
{
  union _ParserStepUserData data;
  data.token_type = type;
  return data;
}

static union _ParserStepUserData
_user_data_node_type(sl_ASTNodeType type)
{
  union _ParserStepUserData data;
  data.node_type = type;
  return data;
}

static union _ParserStepUserData
_user_data_node_number(int number)
{
  union _ParserStepUserData data;
  data.number = number;
  return data;
}

static void
_add_step_to_stack(struct _ParserState *state, parser_step_exec_t exec,
  union _ParserStepUserData user_data)
{
  struct _ParserStep step;
  if (state == NULL)
    return;
  if (exec == NULL)
    return;
  step.exec = exec;
  step.user_data = user_data;
  ARR_APPEND(state->stack, step);
}

static bool
_next_is_keyword(struct _ParserState *state, const char *keyword)
{
  if (state == NULL)
    return FALSE;
  if (keyword == NULL)
    return FALSE;
  if (sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_Identifier
    && strslicecmp2(sl_lexer_get_current_token_string_value(state->input),
    keyword) == 0)
    return TRUE;
  return FALSE;
}

static bool
_next_is_identifier(struct _ParserState *state)
{
  if (state == NULL)
    return FALSE;
  if (sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_Identifier)
    return TRUE;
  return FALSE;
}

static bool
_next_is_type(struct _ParserState *state, sl_LexerTokenType symbol)
{
  if (state == NULL)
    return FALSE;
  if (sl_lexer_get_current_token_type(state->input) == symbol)
    return TRUE;
  return FALSE;
}

static int
_advance(struct _ParserState *state)
{
  int err = sl_lexer_advance(state->input);
  if (err != 0)
    return err;
  return sl_lexer_clear_unused(state->input);
}

static sl_ASTNode *
_current(struct _ParserState *state)
{
  return state->current;
}

static struct _ParserStep *
_get_top(struct _ParserState *state)
{
  if (state == NULL)
    return NULL;
  if (ARR_LENGTH(state->stack) == 0)
    return NULL;
  return ARR_GET(state->stack, ARR_LENGTH(state->stack) - 1);
}

static void
_remove_top(struct _ParserState *state)
{
  if (state == NULL)
    return;
  if (ARR_LENGTH(state->stack) == 0)
    return;
  ARR_POP(state->stack);
}

static int
_consume_keyword(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (!_next_is_keyword(state, user_data.user_str))
    return 1;
  return _advance(state);
}

static int
_consume_name(struct _ParserState *state, union _ParserStepUserData user_data)
{
  if (sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_Identifier
    || sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_String)
  {
    _current(state)->name =
      slice_to_string(sl_lexer_get_current_token_string_value(state->input));
  }
  else
  {
    return 1;
  }
  return _advance(state);
}

static int
_consume_symbol(struct _ParserState *state, union _ParserStepUserData user_data)
{
  if (sl_lexer_get_current_token_type(state->input) ==
    user_data.token_type)
  {
    /* It's ok if this doesn't return 0. In this case, we probably just
       found the end of the file. */
    _advance(state);
    return 0;
  }
  else
  {
    return 1;
  }
}

static int
set_node_location(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _current(state)->line = sl_lexer_get_current_token_line(state->input);
  _current(state)->column = sl_lexer_get_current_token_column(state->input);
  return 0;
}

static int
_descend(struct _ParserState *state, union _ParserStepUserData user_data)
{
  state->current = new_child(state->current);
  state->current->type = user_data.node_type;
  return 0;
}

static int
_ascend(struct _ParserState *state, union _ParserStepUserData user_data)
{
  state->current = state->current->parent;
  return 0;
}

static int
_parse_namespace(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
_parse_binds_flag(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_keyword(state, "binds"))
  {
    _add_step_to_stack(state, &_ascend, _user_data_none());
    _add_step_to_stack(state, &_consume_keyword, _user_data_str("binds"));
    _add_step_to_stack(state, &set_node_location, _user_data_none());
    _add_step_to_stack(state, &_descend,
      _user_data_node_type(sl_ASTNodeType_BindsFlag));
  }
  return 0;
}

static int
_parse_atomic(struct _ParserState *state, union _ParserStepUserData user_data)
{
  if (_next_is_keyword(state, "atomic"))
  {
    _add_step_to_stack(state, &_parse_binds_flag, _user_data_none());
    _add_step_to_stack(state, &_ascend, _user_data_none());
    _add_step_to_stack(state, &_consume_keyword, _user_data_str("atomic"));
    _add_step_to_stack(state, &set_node_location, _user_data_none());
    _add_step_to_stack(state, &_descend,
      _user_data_node_type(sl_ASTNodeType_AtomicFlag));
  }
  return 0;
}

static int
_parse_type(struct _ParserState *state, union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_atomic, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("type"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Type));
  return 0;
}

static int
_parse_path_segment(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
_parse_path_separator(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_Dot))
  {
    _add_step_to_stack(state, &_parse_path_segment, _user_data_none());
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_Dot));
  }
  return 0;
}

static int
_parse_path_segment(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_parse_path_separator, _user_data_none());
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_PathSegment));
  return 0;
}

static int
_parse_path(struct _ParserState *state, union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_path_segment, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Path));
  return 0;
}

static int
parse_import(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("import"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Import));
  return 0;
}

static int
_parse_use(struct _ParserState *state, union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_path, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("use"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Use));
  return 0;
}

static int
_parse_parameter(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
_parse_parameter_separator(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_Comma))
  {
    _add_step_to_stack(state, &_parse_parameter, _user_data_none());
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_Comma));
  }
  return 0;
}

static int
_parse_parameter(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_identifier(state))
  {
    _add_step_to_stack(state, &_parse_parameter_separator, _user_data_none());
    _add_step_to_stack(state, &_ascend, _user_data_none());
    _add_step_to_stack(state, &_parse_path, _user_data_none());
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_Colon));
    _add_step_to_stack(state, &_consume_name, _user_data_none());
    _add_step_to_stack(state, &set_node_location, _user_data_none());
    _add_step_to_stack(state, &_descend,
      _user_data_node_type(sl_ASTNodeType_Parameter));
  }
  return 0;
}

static int
_parse_parameter_list(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_ClosingParenthesis));
  _add_step_to_stack(state, &_parse_parameter, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_OpeningParenthesis));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_ParameterList));
  return 0;
}

static int
_parse_variable(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
_parse_bind(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_variable, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("bind"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Bind));
  return 0;
}

static int
_parse_latex_segment(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
_parse_latex_separator(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_Plus))
  {
    _add_step_to_stack(state, &_parse_latex_segment, _user_data_none());
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_Plus));
  }
  return 0;
}

static int
_parse_latex_string(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_LatexString));
  return 0;
}

static int
_parse_latex_variable(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_DollarSign));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_LatexVariable));
  return 0;
}

static int
_parse_latex_segment(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (_next_is_type(state, sl_LexerTokenType_String))
    exec = &_parse_latex_string;
  else if (_next_is_type(state, sl_LexerTokenType_DollarSign))
    exec = &_parse_latex_variable;
  if (exec != NULL)
  {
    _add_step_to_stack(state, &_parse_latex_separator, _user_data_none());
    _add_step_to_stack(state, exec, _user_data_none());
    return 0;
  }
  else
  {
    return 1;
  }
}

static int
_parse_latex(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_latex_segment, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("latex"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Latex));
  return 0;
}

static int
_parse_value(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
parse_as(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_value, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("as"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_ExpressionAs));
  return 0;
}

static int
_parse_expr_item(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (_next_is_keyword(state, "bind"))
    exec = &_parse_bind;
  else if (_next_is_keyword(state, "latex"))
    exec = &_parse_latex;
  else if (_next_is_keyword(state, "as"))
    exec = &parse_as;
  if (exec != NULL)
  {
    _add_step_to_stack(state, &_parse_expr_item, _user_data_none());
    _add_step_to_stack(state, exec, _user_data_none());
  }
  return 0;
}

static int
_parse_expr_body(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_ClosingBrace));
  _add_step_to_stack(state, &_parse_expr_item, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_OpeningBrace));
  return 0;
}

static int
_parse_expr(struct _ParserState *state, union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_expr_body, _user_data_none());
  _add_step_to_stack(state, &_parse_parameter_list, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &_parse_path, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("expr"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Expression));
  return 0;
}

static int
_parse_const_item(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (_next_is_keyword(state, "latex"))
    exec = &_parse_latex;
  if (exec != NULL)
  {
    _add_step_to_stack(state, &_parse_expr_item, _user_data_none());
    _add_step_to_stack(state, exec, _user_data_none());
  }
  else
  {
    return 1;
  }
  return 0;
}

static int
_parse_const_body(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_OpeningBrace))
  {
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_ClosingBrace));
    _add_step_to_stack(state, &_parse_const_item, _user_data_none());
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_OpeningBrace));
  }
  else
  {
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_Semicolon));
  }
  return 0;
}

static int
_parse_const(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_const_body, _user_data_none());
  _add_step_to_stack(state, &_parse_path, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Colon));
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("const"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_ConstantDeclaration));
  return 0;
}

static int
_parse_variable(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_DollarSign));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Variable));
  return 0;
}

static int
_parse_placeholder(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Percent));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Placeholder));
  return 0;
}

static int
_parse_argument(struct _ParserState *state,
  union _ParserStepUserData user_data);

static int
_parse_argument_separator(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_Comma))
  {
    _add_step_to_stack(state, &_parse_argument, _user_data_none());
    _add_step_to_stack(state, &_consume_symbol,
      _user_data_token_type(sl_LexerTokenType_Comma));
  }
  return 0;
}

static int
_parse_argument(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_identifier(state)
    || _next_is_type(state, sl_LexerTokenType_DollarSign)
    || _next_is_type(state, sl_LexerTokenType_Percent))
  {
    _add_step_to_stack(state, &_parse_argument_separator, _user_data_none());
    _add_step_to_stack(state, &_parse_value, _user_data_none());
  }
  return 0;
}

static int
_parse_argument_list(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_ClosingParenthesis));
  _add_step_to_stack(state, &_parse_argument, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_OpeningParenthesis));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_ArgumentList));
  return 0;
}

static int
_parse_composition_or_constant(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_OpeningParenthesis))
  {
    _add_step_to_stack(state, &_parse_argument_list, _user_data_none());
  }
  else
  {
    _current(state)->type = sl_ASTNodeType_Constant;
  }
  return 0;
}

static int
_parse_composition(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_composition_or_constant,
    _user_data_none());
  _add_step_to_stack(state, &_parse_path, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Composition));
  return 0;
}

static int
_parse_value(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  if (_next_is_type(state, sl_LexerTokenType_DollarSign))
  {
    _add_step_to_stack(state, &_parse_variable, _user_data_none());
  }
  else if (_next_is_type(state, sl_LexerTokenType_Percent))
  {
    _add_step_to_stack(state, &_parse_placeholder, _user_data_none());
  }
  else
  {
    /* TODO: implement lookahead. */
    _add_step_to_stack(state, &_parse_composition, _user_data_none());
  }
  return 0;
}

static int
_parse_assume(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_value, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("assume"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Assume));
  return 0;
}

static int
_parse_infer(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_value, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("infer"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Infer));
  return 0;
}

static int
_parse_require(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_argument_list, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("require"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Require));
  return 0;
}

static int
_parse_def(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_value, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("def"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Def));
  return 0;
}

static int
_parse_axiom_item(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (_next_is_keyword(state, "assume"))
    exec = &_parse_assume;
  else if (_next_is_keyword(state, "infer"))
    exec = &_parse_infer;
  else if (_next_is_keyword(state, "require"))
    exec = &_parse_require;
  else if (_next_is_keyword(state, "def"))
    exec = &_parse_def;
  if (exec != NULL)
  {
    _add_step_to_stack(state, &_parse_axiom_item, _user_data_none());
    _add_step_to_stack(state, exec, _user_data_none());
  }
  return 0;
}

static int
_parse_axiom_body(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_ClosingBrace));
  _add_step_to_stack(state, &_parse_axiom_item, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_OpeningBrace));
  return 0;
}

static int
_parse_axiom(struct _ParserState *state, union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_axiom_body, _user_data_none());
  _add_step_to_stack(state, &_parse_parameter_list, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("axiom"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Axiom));
  return 0;
}

static int
_parse_theorem_reference(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_argument_list, _user_data_none());
  _add_step_to_stack(state, &_parse_path, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_TheoremReference));
  return 0;
}

static int
_parse_step(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_Semicolon));
  _add_step_to_stack(state, &_parse_theorem_reference, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("step"));
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Step));
  return 0;
}

static int
_parse_theorem_item(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (_next_is_keyword(state, "assume"))
    exec = &_parse_assume;
  else if (_next_is_keyword(state, "infer"))
    exec = &_parse_infer;
  else if (_next_is_keyword(state, "require"))
    exec = &_parse_require;
  else if (_next_is_keyword(state, "def"))
    exec = &_parse_def;
  else if (_next_is_keyword(state, "step"))
    exec = &_parse_step;
  if (exec != NULL)
  {
    _add_step_to_stack(state, &_parse_theorem_item, _user_data_none());
    _add_step_to_stack(state, exec, _user_data_none());
  }
  return 0;
}

static int
_parse_theorem_body(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_ClosingBrace));
  _add_step_to_stack(state, &_parse_theorem_item, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_OpeningBrace));
  return 0;
}

static int
_parse_theorem(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_parse_theorem_body, _user_data_none());
  _add_step_to_stack(state, &_parse_parameter_list, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("theorem"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Theorem));
  return 0;
}

static int
_parse_namespace_item(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (_next_is_keyword(state, "namespace"))
    exec = &_parse_namespace;
  else if (_next_is_keyword(state, "import"))
    exec = &parse_import;
  else if (_next_is_keyword(state, "use"))
    exec = &_parse_use;
  else if (_next_is_keyword(state, "type"))
    exec = &_parse_type;
  else if (_next_is_keyword(state, "expr"))
    exec = &_parse_expr;
  else if (_next_is_keyword(state, "const"))
    exec = &_parse_const;
  else if (_next_is_keyword(state, "axiom"))
    exec = &_parse_axiom;
  else if (_next_is_keyword(state, "theorem"))
    exec = &_parse_theorem;
  if (exec != NULL)
  {
    _add_step_to_stack(state, &_parse_namespace_item, _user_data_none());
    _add_step_to_stack(state, exec, _user_data_none());
  }
  return 0;
}

static int
_parse_namespace(struct _ParserState *state,
  union _ParserStepUserData user_data)
{
  _add_step_to_stack(state, &_ascend, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_ClosingBrace));
  _add_step_to_stack(state, &_parse_namespace_item, _user_data_none());
  _add_step_to_stack(state, &_consume_symbol,
    _user_data_token_type(sl_LexerTokenType_OpeningBrace));
  _add_step_to_stack(state, &_consume_name, _user_data_none());
  _add_step_to_stack(state, &set_node_location, _user_data_none());
  _add_step_to_stack(state, &_consume_keyword, _user_data_str("namespace"));
  _add_step_to_stack(state, &_descend,
    _user_data_node_type(sl_ASTNodeType_Namespace));
  return 0;
}

sl_ASTNode *
sl_parse_input(sl_LexerState *input)
{
  struct _ParserState state = {};
  state.input = input;
  state.tree = sl_node_new();
  if (state.tree == NULL)
    return NULL;
  state.tree->type = sl_ASTNodeType_Namespace;
  state.current = state.tree;
  ARR_INIT(state.stack);

  _add_step_to_stack(&state, &_parse_namespace_item, _user_data_none());

  /* Iterate through the stack. */
  sl_lexer_advance(state.input); /* TODO: handle error. */
  sl_lexer_clear_unused(state.input); /* TODO: handle error. */
  while (ARR_LENGTH(state.stack) > 0)
  {
    int err;
    struct _ParserStep *top;

    top = _get_top(&state);
    _remove_top(&state);
    err = top->exec(&state, top->user_data);
    sl_lexer_clear_unused(state.input); /* TODO: handle error. */
    if (err != 0)
    {
      printf("Error parsing (%zu steps on stack)!\n",
        ARR_LENGTH(state.stack));
      break;
    }
  }

  ARR_FREE(state.stack);
  return state.tree;
}
