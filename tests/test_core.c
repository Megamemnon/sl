#include "test_case.h"
#include <logic.h>
#include <core.h>
#include <string.h>

static int
run_test_paths(struct TestState *state)
{
  sl_SymbolPath *path, *path2, *path3;
  char *str;
  sl_LogicState *logic;

  logic = sl_new_logic_state(NULL);
  path = sl_new_symbol_path();
  sl_push_symbol_path(logic, path, "main");
  sl_push_symbol_path(logic, path, "section");
  if (sl_get_symbol_path_length(path) != 2)
  {
    return 1;
  }
  if (strcmp(sl_get_symbol_path_segment(logic, path, 0), "main") != 0)
  {
    return 1;
  }
  if (strcmp(sl_get_symbol_path_segment(logic, path, 1), "section") != 0)
  {
    return 1;
  }
  if (strcmp(sl_get_symbol_path_last_segment(logic, path), "section") != 0)
  {
    return 1;
  }

  path2 = sl_copy_symbol_path(path);
  if (!sl_symbol_paths_equal(path, path2))
  {
    return 1;
  }
  if (!sl_symbol_paths_equal(path2, path))
  {
    return 1;
  }

  sl_push_symbol_path(logic, path2, "item");
  if (sl_symbol_paths_equal(path, path2))
  {
    return 1;
  }
  str = sl_string_from_symbol_path(logic, path2);
  if (strcmp(str, "main.section.item") != 0)
  {
    return 1;
  }
  sl_pop_symbol_path(path2);
  if (!sl_symbol_paths_equal(path, path2))
  {
    return 1;
  }

  path3 = sl_new_symbol_path();
  sl_push_symbol_path(logic, path3, "a");
  sl_push_symbol_path(logic, path3, "b");
  sl_append_symbol_path(path, path3);
  sl_push_symbol_path(logic, path2, "a");
  sl_push_symbol_path(logic, path2, "b");
  if (!sl_symbol_paths_equal(path, path2))
  {
    return 1;
  }

  sl_free_symbol_path(path);
  sl_free_symbol_path(path2);
  sl_free_symbol_path(path3);
  sl_free_logic_state(logic);
  free(str);
  return 0;
}

static int
run_test_namespaces(struct TestState *state)
{
  sl_LogicState *logic;
  logic = sl_new_logic_state(NULL);

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "space");
    if (sl_logic_make_namespace(logic, path) != sl_LogicError_None)
      return 1;
    if (sl_logic_make_namespace(logic, path)
      != sl_LogicError_SymbolAlreadyExists)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "a");
    sl_push_symbol_path(logic, path, "b");
    if (sl_logic_make_namespace(logic, path) != sl_LogicError_NoParent)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "space");
    sl_push_symbol_path(logic, path, "nested");
    if (sl_logic_make_namespace(logic, path) != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  sl_free_logic_state(logic);

  return 0;
}

static int
run_test_types(struct TestState *state)
{
  sl_LogicState *logic;
  logic = sl_new_logic_state(NULL);

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "type1");
    if (sl_logic_make_type(logic, path, FALSE, FALSE, FALSE) != sl_LogicError_None)
      return 1;
    if (sl_logic_make_type(logic, path, FALSE, FALSE, FALSE)
      != sl_LogicError_SymbolAlreadyExists)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "type2");
    if (sl_logic_make_type(logic, path, TRUE, FALSE, FALSE)
        != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "type3");
    if (sl_logic_make_type(logic, path, FALSE, TRUE, FALSE)
      != sl_LogicError_CannotBindNonAtomic)
      return 1;
    if (sl_logic_make_type(logic, path, TRUE, TRUE, FALSE)
        != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "a");
    sl_push_symbol_path(logic, path, "b");
    if (sl_logic_make_type(logic, path, FALSE, FALSE, FALSE) != sl_LogicError_NoParent)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "type3");
    sl_push_symbol_path(logic, path, "child");
    if (sl_logic_make_type(logic, path, FALSE, FALSE, FALSE)
        != sl_LogicError_NoParent)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *namespace_path, *type_path;
    namespace_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, namespace_path, "container");
    type_path = sl_copy_symbol_path(namespace_path);
    sl_push_symbol_path(logic, type_path, "type");
    if (sl_logic_make_namespace(logic, namespace_path) != sl_LogicError_None)
      return 1;
    if (sl_logic_make_type(logic, type_path, FALSE, FALSE, FALSE)
      != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(namespace_path);
    sl_free_symbol_path(type_path);
  }

  sl_free_logic_state(logic);
  return 0;
}

static int run_test_blocks(struct TestState *state)
{
  sl_LogicState *logic;
  logic = sl_new_logic_state(NULL);

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "type1");
    if (sl_logic_make_type(logic, path, FALSE, FALSE, FALSE)
        != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "type2");
    if (sl_logic_make_type(logic, path, FALSE, FALSE, FALSE)
        != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  /* Creating a block with a parameter of a type that does not exist. */
  {
    sl_ParametrizedBlock *block;
    struct sl_PrototypeParameter param1;
    param1.name = "param1";
    param1.type_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, param1.type_path, "type_bad");
    {
      struct sl_PrototypeParameter *params[] = { &param1, NULL };
      if (sl_logic_make_block(logic, params, &block)
          != sl_LogicError_NoType)
        return 1;
    }
    sl_free_symbol_path(param1.type_path);
  }

  /* Creating a block with repeated parameters. */
  {
    sl_ParametrizedBlock *block;
    struct sl_PrototypeParameter param1, param2;
    param1.name = "param1";
    param1.type_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, param1.type_path, "type1");
    param2.name = "param1";
    param2.type_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, param2.type_path, "type2");
    {
      struct sl_PrototypeParameter *params[] = { &param1, &param2, NULL };
      if (sl_logic_make_block(logic, params, &block)
          != sl_LogicError_RepeatedParameter)
        return 1;
    }
    sl_free_symbol_path(param1.type_path);
    sl_free_symbol_path(param2.type_path);
  }

  /* Creating a block with OK parameters. */
  {
    sl_ParametrizedBlock *block;
    struct sl_PrototypeParameter param1, param2, param3;
    param1.name = "p1";
    param1.type_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, param1.type_path, "type1");
    param2.name = "p2";
    param2.type_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, param2.type_path, "type2");
    param3.name = "p3";
    param3.type_path = sl_new_symbol_path();
    sl_push_symbol_path(logic, param3.type_path, "type2");
    {
      struct sl_PrototypeParameter *params[] = { &param1, &param2, &param3,
          NULL };
      if (sl_logic_make_block(logic, params, &block) != sl_LogicError_None)
        return 1;
      if (block == NULL)
        return 1;
    }
    sl_logic_free_block(block);
    sl_free_symbol_path(param1.type_path);
    sl_free_symbol_path(param2.type_path);
    sl_free_symbol_path(param3.type_path);
  }

  sl_free_logic_state(logic);
  return 0;
}

static int
run_test_constants(struct TestState *state)
{
  sl_LogicState *logic;
  sl_SymbolPath *type_path;
  logic = sl_new_logic_state(NULL);

  type_path = sl_new_symbol_path();
  sl_push_symbol_path(logic, type_path, "type_A");
  if (sl_logic_make_type(logic, type_path, FALSE, FALSE, FALSE)
      != sl_LogicError_None)
    return 1;

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "c1");
    if (sl_logic_make_constant(logic, path, type_path, NULL)
      != sl_LogicError_None)
      return 1;
    if (sl_logic_make_constant(logic, path, type_path, NULL)
      != sl_LogicError_SymbolAlreadyExists)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *type_path2;
    sl_SymbolPath *path;
    type_path2 = sl_new_symbol_path();
    sl_push_symbol_path(logic, type_path2, "fake_type");
    path = sl_new_symbol_path();
    sl_push_symbol_path(logic, path, "c2");
    if (sl_logic_make_constant(logic, path, type_path2, NULL)
      != sl_LogicError_NoType)
      return 1;
    sl_free_symbol_path(type_path2);
    sl_free_symbol_path(path);
  }

  sl_free_symbol_path(type_path);
  sl_free_logic_state(logic);
  return 0;
}

static int
run_test_values(struct TestState *state)
{
  return 0;
}

static int
run_test_require(struct TestState *state)
{
  return 0;
}

struct TestCase test_paths = { "Paths", &run_test_paths };
struct TestCase test_namespaces = { "Namespaces", &run_test_namespaces };
struct TestCase test_types = { "Types", &run_test_types };
struct TestCase test_blocks = { "Blocks", &run_test_blocks };
struct TestCase test_constants = { "Constants", &run_test_constants };
struct TestCase test_values = { "Values", &run_test_values };
struct TestCase test_require = { "Require", &run_test_require };
