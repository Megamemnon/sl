#include "parse.h"
#include "common.h"
#include <string.h>

struct sl_ASTNode {
  size_t index;
  size_t parent_index;
  size_t first_child_index;
  size_t left_sibling_index;
  size_t right_sibling_index;

  sl_ASTNodeType type;
  size_t line;
  size_t column;
  char *name;
};

struct sl_ASTContainer {
  ARR(sl_ASTNode) nodes;
  size_t root_index;
};

int verbose = 0;

static sl_ASTNode * sl_ast_container_get_root_mutable(
    sl_ASTContainer *container)
{
  if (container == NULL)
    return NULL;
  if (container->root_index == SIZE_MAX)
    return NULL;
  return ARR_GET(container->nodes, container->root_index);
}

const sl_ASTNode * sl_ast_container_get_root(const sl_ASTContainer *container)
{
  if (container == NULL)
    return NULL;
  if (container->root_index == SIZE_MAX)
    return NULL;
  return ARR_GET(container->nodes, container->root_index);
}

static const sl_ASTNode * sl_ast_container_get_node(const sl_ASTContainer
    *container, size_t index)
{
  return ARR_GET(container->nodes, index);
}

static sl_ASTNode * sl_ast_container_get_node_mutable(sl_ASTContainer
    *container, size_t index)
{
  return ARR_GET(container->nodes, index);
}

const sl_ASTNode * sl_node_get_parent(const sl_ASTContainer *container,
    const sl_ASTNode *node)
{
  if (container == NULL || node == NULL)
    return NULL;
  return ARR_GET(container->nodes, node->parent_index);
}

size_t sl_node_get_child_count(const sl_ASTContainer *container,
    const sl_ASTNode *node)
{
  size_t n, index;
  if (node == NULL)
    return 0;
  n = 0;
  index = node->first_child_index;
  while (index != SIZE_MAX) {
    const sl_ASTNode *child;
    child = sl_ast_container_get_node(container, index);
    index = child->right_sibling_index;
    ++n;
  }
  return n;
}

const sl_ASTNode * sl_node_get_child(const sl_ASTContainer *container,
    const sl_ASTNode *node, size_t child_index)
{
  const sl_ASTNode *child;
  size_t index;
  if (node == NULL)
    return NULL;
  if (child_index >= sl_node_get_child_count(container, node))
    return NULL;
  index = node->first_child_index;
  child = sl_ast_container_get_node(container, index);
  for (size_t i = 0; i < child_index; ++i) {
    index = child->right_sibling_index;
    child = sl_ast_container_get_node(container, index);
  }
  return child;
}

static sl_ASTNode * sl_node_get_child_mutable(sl_ASTContainer *container,
    sl_ASTNode *node, size_t child_index)
{
  sl_ASTNode *child;
  size_t index;
  if (node == NULL)
    return NULL;
  if (child_index >= sl_node_get_child_count(container, node))
    return NULL;
  index = node->first_child_index;
  child = sl_ast_container_get_node_mutable(container, index);
  for (size_t i = 0; i < child_index; ++i) {
    index = child->right_sibling_index;
    child = sl_ast_container_get_node_mutable(container, index);
  }
  return child;
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

static void free_children(sl_ASTContainer *container, sl_ASTNode *root)
{
  for (size_t i = 0; i < sl_node_get_child_count(container, root); ++i)
  {
    sl_ASTNode *child = sl_node_get_child_mutable(container, root, i);
    free_children(container, child);
  }
  if (root->name != NULL)
    free(root->name);
}

void sl_ast_container_free(sl_ASTContainer *container)
{
  free_children(container, sl_ast_container_get_root_mutable(container));
  ARR_FREE(container->nodes);
  free(container);
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
    case sl_ASTNodeType_DummyFlag:
      snprintf(buf, len, "Dummy<>");
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
    case sl_ASTNodeType_Builtin:
      snprintf(buf, len, "Builtin<\"%s\">", node->name);
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

static void print_children(const sl_ASTContainer *container,
    const sl_ASTNode *root, unsigned int depth)
{
  for (size_t i = 0; i < depth; ++i)
    printf(" ");
  char buf[1024];
  print_node(buf, 1024, root);
  printf("%s\n", buf);
  for (size_t i = 0; i < sl_node_get_child_count(container, root); ++i) {
    print_children(container, sl_node_get_child(container, root, i),
        depth + 1);
  }
}

void sl_ast_print(const sl_ASTContainer *container)
{
  print_children(container, sl_ast_container_get_root(container), 0);
}

void
sl_node_show_message(sl_TextInput *input, const sl_ASTNode *node,
  const char *message, sl_MessageType type)
{
  sl_input_show_message(input, node->line, node->column, message, type);
}

static sl_ASTNode * sl_node_new(sl_ASTContainer *container)
{
  sl_ASTNode node;
  node.index = ARR_LENGTH(container->nodes);
  node.parent_index = SIZE_MAX;
  node.first_child_index = SIZE_MAX;
  node.left_sibling_index = SIZE_MAX;
  node.right_sibling_index = SIZE_MAX;
  node.name = NULL;
  ARR_APPEND(container->nodes, node);
  return ARR_GET(container->nodes, node.index);
}

static sl_ASTNode * new_child(sl_ASTContainer *container, sl_ASTNode *parent)
{
  sl_ASTNode *child, *parent_node;
  size_t parent_index = parent->index;
  child = sl_node_new(container);
  child->parent_index = parent_index;
  parent_node = sl_ast_container_get_node_mutable(container, parent_index);
  if (sl_node_get_child_count(container, parent_node) > 0) {
    sl_ASTNode *sibling = sl_node_get_child_mutable(container, parent_node,
        sl_node_get_child_count(container, parent_node) - 1);
    sibling->right_sibling_index = child->index;
    child->left_sibling_index = sibling->index;
  } else {
    parent_node->first_child_index = child->index;
  }
  return child;
}

static sl_ASTContainer * new_container()
{
  sl_ASTContainer *container;
  container = SL_NEW(sl_ASTContainer);
  if (container == NULL)
    return NULL;
  ARR_INIT(container->nodes);
  sl_node_new(container);
  container->root_index = 0;
  return container;
}

/* --- Parser --- */
struct ParserState;

/* Return nonzero to indicate an error. */
union ParserStepUserData
{
  const char *user_str;
  sl_LexerTokenType token_type;
  sl_ASTNodeType node_type;
  int number;
};

typedef int (* parser_step_exec_t)(struct ParserState *,
  union ParserStepUserData);

struct ParserStep
{
  parser_step_exec_t exec;
  union ParserStepUserData user_data;
};

struct ParserState
{
  sl_LexerState *input;
  sl_ASTContainer *container;
  size_t current_node_index;
  bool panic;

  ARR(struct ParserStep) stack;
};

static union ParserStepUserData
user_data_str(const char *str)
{
  union ParserStepUserData data;
  data.user_str = str;
  return data;
}

static union ParserStepUserData
user_data_none()
{
  return user_data_str(NULL);
}

static union ParserStepUserData
user_data_token_type(sl_LexerTokenType type)
{
  union ParserStepUserData data;
  data.token_type = type;
  return data;
}

static union ParserStepUserData
user_data_node_type(sl_ASTNodeType type)
{
  union ParserStepUserData data;
  data.node_type = type;
  return data;
}

static union ParserStepUserData
user_data_node_number(int number)
{
  union ParserStepUserData data;
  data.number = number;
  return data;
}

static void
add_step_to_stack(struct ParserState *state, parser_step_exec_t exec,
  union ParserStepUserData user_data)
{
  struct ParserStep step;
  if (state == NULL)
    return;
  if (exec == NULL)
    return;
  step.exec = exec;
  step.user_data = user_data;
  ARR_APPEND(state->stack, step);
}

static bool
next_is_keyword(struct ParserState *state, const char *keyword)
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
next_is_identifier(struct ParserState *state)
{
  if (state == NULL)
    return FALSE;
  if (sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_Identifier)
    return TRUE;
  return FALSE;
}

static bool
next_is_type(struct ParserState *state, sl_LexerTokenType symbol)
{
  if (state == NULL)
    return FALSE;
  if (sl_lexer_get_current_token_type(state->input) == symbol)
    return TRUE;
  return FALSE;
}

static int
advance(struct ParserState *state)
{
  int err = sl_lexer_advance(state->input);
  if (err != 0)
    return err;
  return sl_lexer_clear_unused(state->input);
}

static sl_ASTNode *
current(struct ParserState *state)
{
  return sl_ast_container_get_node_mutable(state->container,
      state->current_node_index);
}

static struct ParserStep *
get_top(struct ParserState *state)
{
  if (state == NULL)
    return NULL;
  if (ARR_LENGTH(state->stack) == 0)
    return NULL;
  return ARR_GET(state->stack, ARR_LENGTH(state->stack) - 1);
}

static void
remove_top(struct ParserState *state)
{
  if (state == NULL)
    return;
  if (ARR_LENGTH(state->stack) == 0)
    return;
  ARR_POP(state->stack);
}

static int
consume_keyword(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (!next_is_keyword(state, user_data.user_str))
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Expected a keyword.", sl_MessageType_Error);
    return 1;
  }
  return advance(state);
}

static int
consume_name(struct ParserState *state, union ParserStepUserData user_data)
{
  if (sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_Identifier
    || sl_lexer_get_current_token_type(state->input)
    == sl_LexerTokenType_String)
  {
    current(state)->name =
      slice_to_string(sl_lexer_get_current_token_string_value(state->input));
  }
  else
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Expected an identifier.", sl_MessageType_Error);
    return 1;
  }
  return advance(state);
}

static int
consume_symbol(struct ParserState *state, union ParserStepUserData user_data)
{
  if (sl_lexer_get_current_token_type(state->input) ==
    user_data.token_type)
  {
    /* It's ok if this doesn't return 0. In this case, we probably just
       found the end of the file. */
    advance(state);
    return 0;
  }
  else
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Expected a symbol.", sl_MessageType_Error);
    return 1;
  }
}

static int
set_node_location(struct ParserState *state,
  union ParserStepUserData user_data)
{
  current(state)->line = sl_lexer_get_current_token_line(state->input);
  current(state)->column = sl_lexer_get_current_token_column(state->input);
  return 0;
}

static int
descend(struct ParserState *state, union ParserStepUserData user_data)
{
  state->current_node_index =
      new_child(state->container, current(state))->index;
  current(state)->type = user_data.node_type;
  return 0;
}

static int
ascend(struct ParserState *state, union ParserStepUserData user_data)
{
  state->current_node_index = current(state)->parent_index;
  return 0;
}

static int
parse_namespace(struct ParserState *state,
  union ParserStepUserData user_data);

static int parse_type_flag(struct ParserState *state,
    union ParserStepUserData user_data);

static int parse_dummy_flag(struct ParserState *state,
    union ParserStepUserData user_data)
{
  if (next_is_keyword(state, "dummy")) {
    add_step_to_stack(state, &parse_type_flag, user_data_none());
    add_step_to_stack(state, &ascend, user_data_none());
    add_step_to_stack(state, &consume_keyword, user_data_str("dummy"));
    add_step_to_stack(state, &set_node_location, user_data_none());
    add_step_to_stack(state, &descend,
        user_data_node_type(sl_ASTNodeType_DummyFlag));
  }
  return 0;
}

static int parse_binds_flag(struct ParserState *state,
    union ParserStepUserData user_data)
{
  if (next_is_keyword(state, "binds")) {
    add_step_to_stack(state, &parse_type_flag, user_data_none());
    add_step_to_stack(state, &ascend, user_data_none());
    add_step_to_stack(state, &consume_keyword, user_data_str("binds"));
    add_step_to_stack(state, &set_node_location, user_data_none());
    add_step_to_stack(state, &descend,
        user_data_node_type(sl_ASTNodeType_BindsFlag));
  }
  return 0;
}

static int parse_atomic(struct ParserState *state,
    union ParserStepUserData user_data)
{
  if (next_is_keyword(state, "atomic")) {
    add_step_to_stack(state, &parse_type_flag, user_data_none());
    add_step_to_stack(state, &ascend, user_data_none());
    add_step_to_stack(state, &consume_keyword, user_data_str("atomic"));
    add_step_to_stack(state, &set_node_location, user_data_none());
    add_step_to_stack(state, &descend,
        user_data_node_type(sl_ASTNodeType_AtomicFlag));
  }
  return 0;
}

static int parse_type_flag(struct ParserState *state,
    union ParserStepUserData user_data)
{
  if (next_is_keyword(state, "dummy"))
    add_step_to_stack(state, &parse_dummy_flag, user_data_none());
  else if (next_is_keyword(state, "binds"))
    add_step_to_stack(state, &parse_binds_flag, user_data_none());
  else if (next_is_keyword(state, "atomic"))
    add_step_to_stack(state, &parse_atomic, user_data_none());
  return 0;
}

static int parse_type(struct ParserState *state,
    union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_type_flag, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("type"));
  add_step_to_stack(state, &descend,
      user_data_node_type(sl_ASTNodeType_Type));
  return 0;
}

static int
parse_path_segment(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_path_separator(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_Dot))
  {
    add_step_to_stack(state, &parse_path_segment, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Dot));
  }
  return 0;
}

static int
parse_path_segment(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &parse_path_separator, user_data_none());
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_PathSegment));
  return 0;
}

static int
parse_path(struct ParserState *state, union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_path_segment, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Path));
  return 0;
}

static int
parse_import(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("import"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Import));
  return 0;
}

static int
parse_use(struct ParserState *state, union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_path, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("use"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Use));
  return 0;
}

static int
parse_parameter(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_parameter_separator(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_Comma))
  {
    add_step_to_stack(state, &parse_parameter, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Comma));
  }
  return 0;
}

static int
parse_parameter(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_identifier(state))
  {
    add_step_to_stack(state, &parse_parameter_separator, user_data_none());
    add_step_to_stack(state, &ascend, user_data_none());
    add_step_to_stack(state, &parse_path, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Colon));
    add_step_to_stack(state, &consume_name, user_data_none());
    add_step_to_stack(state, &set_node_location, user_data_none());
    add_step_to_stack(state, &descend,
      user_data_node_type(sl_ASTNodeType_Parameter));
  }
  return 0;
}

static int
parse_parameter_list(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingParenthesis));
  add_step_to_stack(state, &parse_parameter, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningParenthesis));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_ParameterList));
  return 0;
}

static int
parse_variable(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_bind(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_variable, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("bind"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Bind));
  return 0;
}

static int
parse_latex_segment(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_latex_separator(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_Plus))
  {
    add_step_to_stack(state, &parse_latex_segment, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Plus));
  }
  return 0;
}

static int
parse_latex_string(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_LatexString));
  return 0;
}

static int
parse_latex_variable(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_DollarSign));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_LatexVariable));
  return 0;
}

static int
parse_latex_segment(struct ParserState *state,
  union ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (next_is_type(state, sl_LexerTokenType_String))
    exec = &parse_latex_string;
  else if (next_is_type(state, sl_LexerTokenType_DollarSign))
    exec = &parse_latex_variable;
  if (exec != NULL)
  {
    add_step_to_stack(state, &parse_latex_separator, user_data_none());
    add_step_to_stack(state, exec, user_data_none());
    return 0;
  }
  else
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Expected a string or a variable in LaTeX expression.",
      sl_MessageType_Error);
    return 1;
  }
}

static int
parse_latex(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_latex_segment, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("latex"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Latex));
  return 0;
}

static int
parse_value(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_as(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_value, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("as"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_ExpressionAs));
  return 0;
}

static int
parse_expr_item(struct ParserState *state,
  union ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (next_is_keyword(state, "bind"))
  {
    exec = &parse_bind;
  }
  else if (next_is_keyword(state, "latex"))
  {
    exec = &parse_latex;
  }
  else if (next_is_keyword(state, "as"))
  {
    exec = &parse_as;
  }
  else if (!next_is_type(state, sl_LexerTokenType_ClosingBrace))
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Unknown expression in expression body.", sl_MessageType_Error);
  }
  if (exec != NULL)
  {
    add_step_to_stack(state, &parse_expr_item, user_data_none());
    add_step_to_stack(state, exec, user_data_none());
  }
  return 0;
}

static int
parse_expr_body(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingBrace));
  add_step_to_stack(state, &parse_expr_item, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningBrace));
  return 0;
}

static int
parse_expr(struct ParserState *state, union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_expr_body, user_data_none());
  add_step_to_stack(state, &parse_parameter_list, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &parse_path, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("expr"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Expression));
  return 0;
}

static int
parse_const_item(struct ParserState *state,
  union ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (next_is_keyword(state, "latex"))
  {
    exec = &parse_latex;
  }
  else if (!next_is_type(state, sl_LexerTokenType_ClosingBrace))
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Unknown expression in constant body.", sl_MessageType_Error);
  }
  if (exec != NULL)
  {
    add_step_to_stack(state, &parse_expr_item, user_data_none());
    add_step_to_stack(state, exec, user_data_none());
  }
  return 0;
}

static int
parse_const_body(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_OpeningBrace))
  {
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_ClosingBrace));
    add_step_to_stack(state, &parse_const_item, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_OpeningBrace));
  }
  else
  {
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Semicolon));
  }
  return 0;
}

static int
parse_const(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_const_body, user_data_none());
  add_step_to_stack(state, &parse_path, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Colon));
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("const"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_ConstantDeclaration));
  return 0;
}

static int
parse_constspace(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_path,
    user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("constspace"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Constspace));
  return 0;
}

static int
parse_variable(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_DollarSign));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Variable));
  return 0;
}

static int
parse_placeholder(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Percent));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Placeholder));
  return 0;
}

static int
parse_argument(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_argument_separator(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_Comma))
  {
    add_step_to_stack(state, &parse_argument, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Comma));
  }
  return 0;
}

static int
parse_argument(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_identifier(state)
    || next_is_type(state, sl_LexerTokenType_DollarSign)
    || next_is_type(state, sl_LexerTokenType_Percent))
  {
    add_step_to_stack(state, &parse_argument_separator, user_data_none());
    add_step_to_stack(state, &parse_value, user_data_none());
  }
  return 0;
}

static int
parse_argument_list(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingParenthesis));
  add_step_to_stack(state, &parse_argument, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningParenthesis));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_ArgumentList));
  return 0;
}

static int
parse_composition_or_constant(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_OpeningParenthesis))
  {
    add_step_to_stack(state, &parse_argument_list, user_data_none());
  }
  else
  {
    current(state)->type = sl_ASTNodeType_Constant;
  }
  return 0;
}

static int
parse_composition(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_composition_or_constant,
    user_data_none());
  add_step_to_stack(state, &parse_path, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Composition));
  return 0;
}

static int
parse_builtin_argument(struct ParserState *state,
  union ParserStepUserData user_data);

static int
parse_builtin_argument_separator(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_Comma))
  {
    add_step_to_stack(state, &parse_builtin_argument, user_data_none());
    add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_Comma));
  }
  return 0;
}

static int
parse_builtin_argument(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (!next_is_type(state, sl_LexerTokenType_ClosingParenthesis)) {
    add_step_to_stack(state, &parse_builtin_argument_separator,
        user_data_none());
    add_step_to_stack(state, &parse_path, user_data_none());
  }
  return 0;
}

static int
parse_builtin_argument_list(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingParenthesis));
  add_step_to_stack(state, &parse_builtin_argument, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningParenthesis));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_ArgumentList));
  return 0;
}

static int parse_builtin(struct ParserState *state,
    union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_builtin_argument_list, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_symbol,
      user_data_token_type(sl_LexerTokenType_At));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Builtin));
  return 0;
}

static int
parse_value(struct ParserState *state,
  union ParserStepUserData user_data)
{
  if (next_is_type(state, sl_LexerTokenType_DollarSign)) {
    add_step_to_stack(state, &parse_variable, user_data_none());
  } else if (next_is_type(state, sl_LexerTokenType_Percent)) {
    add_step_to_stack(state, &parse_placeholder, user_data_none());
  } else if (next_is_type(state, sl_LexerTokenType_At)) {
    add_step_to_stack(state, &parse_builtin, user_data_none());
  } else {
    /* TODO: implement lookahead. */
    add_step_to_stack(state, &parse_composition, user_data_none());
  }
  return 0;
}

static int
parse_assume(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_value, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("assume"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Assume));
  return 0;
}

static int
parse_infer(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_value, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("infer"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Infer));
  return 0;
}

static int
parse_require(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_argument_list, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("require"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Require));
  return 0;
}

static int
parse_def(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_value, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("def"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Def));
  return 0;
}

static int
parse_axiom_item(struct ParserState *state,
  union ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (next_is_keyword(state, "assume"))
  {
    exec = &parse_assume;
  }
  else if (next_is_keyword(state, "infer"))
  {
    exec = &parse_infer;
  }
  else if (next_is_keyword(state, "require"))
  {
    exec = &parse_require;
  }
  else if (next_is_keyword(state, "def"))
  {
    exec = &parse_def;
  } else if (!next_is_type(state, sl_LexerTokenType_ClosingBrace)) {
    sl_lexer_show_message_at_current_token(state->input,
      "Unknown expression in axiom body.", sl_MessageType_Error);
  }
  if (exec != NULL)
  {
    add_step_to_stack(state, &parse_axiom_item, user_data_none());
    add_step_to_stack(state, exec, user_data_none());
  }
  return 0;
}

static int
parse_axiom_body(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingBrace));
  add_step_to_stack(state, &parse_axiom_item, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningBrace));
  return 0;
}

static int
parse_axiom(struct ParserState *state, union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_axiom_body, user_data_none());
  add_step_to_stack(state, &parse_parameter_list, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("axiom"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Axiom));
  return 0;
}

static int
parse_theorem_reference(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_argument_list, user_data_none());
  add_step_to_stack(state, &parse_path, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_TheoremReference));
  return 0;
}

static int
parse_step(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_Semicolon));
  add_step_to_stack(state, &parse_theorem_reference, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("step"));
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Step));
  return 0;
}

static int
parse_theorem_item(struct ParserState *state,
  union ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (next_is_keyword(state, "assume"))
  {
    exec = &parse_assume;
  }
  else if (next_is_keyword(state, "infer"))
  {
    exec = &parse_infer;
  }
  else if (next_is_keyword(state, "require"))
  {
    exec = &parse_require;
  }
  else if (next_is_keyword(state, "def"))
  {
    exec = &parse_def;
  } else if (next_is_keyword(state, "step")) {
    exec = &parse_step;
  }
  else if (!next_is_type(state, sl_LexerTokenType_ClosingBrace))
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Unknown expression in theorem body.", sl_MessageType_Error);
  }
  if (exec != NULL)
  {
    add_step_to_stack(state, &parse_theorem_item, user_data_none());
    add_step_to_stack(state, exec, user_data_none());
  }
  return 0;
}

static int
parse_theorem_body(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingBrace));
  add_step_to_stack(state, &parse_theorem_item, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningBrace));
  return 0;
}

static int
parse_theorem(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &parse_theorem_body, user_data_none());
  add_step_to_stack(state, &parse_parameter_list, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("theorem"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Theorem));
  return 0;
}

static int
parse_namespace_item(struct ParserState *state,
  union ParserStepUserData user_data)
{
  parser_step_exec_t exec;
  exec = NULL;
  if (next_is_keyword(state, "namespace"))
  {
    exec = &parse_namespace;
  }
  else if (next_is_keyword(state, "import"))
  {
    exec = &parse_import;
  }
  else if (next_is_keyword(state, "use"))
  {
    exec = &parse_use;
  }
  else if (next_is_keyword(state, "type"))
  {
    exec = &parse_type;
  }
  else if (next_is_keyword(state, "expr"))
  {
    exec = &parse_expr;
  }
  else if (next_is_keyword(state, "const"))
  {
    exec = &parse_const;
  }
  else if (next_is_keyword(state, "constspace"))
  {
    exec = &parse_constspace;
  }
  else if (next_is_keyword(state, "axiom"))
  {
    exec = &parse_axiom;
  }
  else if (next_is_keyword(state, "theorem"))
  {
    exec = &parse_theorem;
  }
  else if (!next_is_type(state, sl_LexerTokenType_ClosingBrace) &&
    !sl_lexer_done(state->input))
  {
    sl_lexer_show_message_at_current_token(state->input,
      "Unknown expression in namespace body.", sl_MessageType_Error);
  }
  if (exec != NULL)
  {
    add_step_to_stack(state, &parse_namespace_item, user_data_none());
    add_step_to_stack(state, exec, user_data_none());
  }
  return 0;
}

static int
parse_namespace(struct ParserState *state,
  union ParserStepUserData user_data)
{
  add_step_to_stack(state, &ascend, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_ClosingBrace));
  add_step_to_stack(state, &parse_namespace_item, user_data_none());
  add_step_to_stack(state, &consume_symbol,
    user_data_token_type(sl_LexerTokenType_OpeningBrace));
  add_step_to_stack(state, &consume_name, user_data_none());
  add_step_to_stack(state, &set_node_location, user_data_none());
  add_step_to_stack(state, &consume_keyword, user_data_str("namespace"));
  add_step_to_stack(state, &descend,
    user_data_node_type(sl_ASTNodeType_Namespace));
  return 0;
}

sl_ASTContainer * sl_parse_input(sl_LexerState *input, int *error)
{
  struct ParserState state = {};
  state.input = input;
  state.container = new_container();
  if (state.container == NULL)
    return NULL;
  sl_ast_container_get_root_mutable(state.container)->type =
      sl_ASTNodeType_Namespace;
  state.current_node_index = state.container->root_index;
  state.panic = FALSE;
  ARR_INIT(state.stack);

  add_step_to_stack(&state, &parse_namespace_item, user_data_none());

  /* Iterate through the stack. */
  sl_lexer_advance(state.input); /* TODO: handle error. */
  sl_lexer_clear_unused(state.input); /* TODO: handle error. */
  while (ARR_LENGTH(state.stack) > 0)
  {
    int err;
    struct ParserStep *top;

    top = get_top(&state);
    remove_top(&state);
    err = top->exec(&state, top->user_data);
    sl_lexer_clear_unused(state.input); /* TODO: handle error. */
    if (err != 0)
    {
      state.panic = TRUE;
      printf("Error parsing (%zu steps on stack)!\n",
        ARR_LENGTH(state.stack));
      break;
    }
  }

  ARR_FREE(state.stack);
  if (error != NULL)
    *error = 0;
  return state.container;
}
