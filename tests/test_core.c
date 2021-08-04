#include "test_case.h"
#include <logic.h>
#include <core.h>
#include <string.h>

static int
run_test_paths(struct TestState *state)
{
  sl_SymbolPath *path, *path2, *path3;
  char *str;

  path = sl_new_symbol_path();
  sl_push_symbol_path(path, "main");
  sl_push_symbol_path(path, "section");
  if (sl_get_symbol_path_length(path) != 2)
  {
    return 1;
  }
  if (strcmp(sl_get_symbol_path_segment(path, 0), "main") != 0)
  {
    return 1;
  }
  if (strcmp(sl_get_symbol_path_segment(path, 1), "section") != 0)
  {
    return 1;
  }
  if (strcmp(sl_get_symbol_path_last_segment(path), "section") != 0)
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

  sl_push_symbol_path(path2, "item");
  if (sl_symbol_paths_equal(path, path2))
  {
    return 1;
  }
  str = sl_string_from_symbol_path(path2);
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
  sl_push_symbol_path(path3, "a");
  sl_push_symbol_path(path3, "b");
  sl_append_symbol_path(path, path3);
  sl_push_symbol_path(path2, "a");
  sl_push_symbol_path(path2, "b");
  if (!sl_symbol_paths_equal(path, path2))
  {
    return 1;
  }

  sl_free_symbol_path(path);
  sl_free_symbol_path(path2);
  sl_free_symbol_path(path3);
  free(str);
  return 0;
}

static int
run_test_namespaces(struct TestState *state)
{
  return 0; /* TODO: tmp */

  sl_LogicState *logic;
  logic = new_logic_state(NULL);

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(path, "space");
    if (sl_logic_make_namespace(logic, path) != sl_LogicError_None)
      return 1;
  }

  free_logic_state(logic);

  return 0;
}

static int
run_test_types(struct TestState *state)
{
  sl_LogicState *logic;
  logic = new_logic_state(NULL);

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(path, "type1");
    if (add_type(logic, path, FALSE, FALSE) != sl_LogicError_None)
      return 1;
    if (add_type(logic, path, FALSE, FALSE)
      != sl_LogicError_SymbolAlreadyExists)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(path, "type2");
    if (add_type(logic, path, TRUE, FALSE) != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = sl_new_symbol_path();
    sl_push_symbol_path(path, "type3");
    if (add_type(logic, path, FALSE, TRUE)
      != sl_LogicError_CannotBindNonAtomic)
      return 1;
    if (add_type(logic, path, TRUE, TRUE) != sl_LogicError_None)
      return 1;
    sl_free_symbol_path(path);
  }

  free_logic_state(logic);
  return 0;
}

static int
run_test_values(struct TestState *state)
{
  return 0;
}

static sl_LogicState *
prepare_test_require()
{
  return new_logic_state(stdout);
}

static int
run_test_require(sl_LogicState *state)
{
  /* Test distinctness. */

  return 0;
}

static void
cleanup_test_require(sl_LogicState *state)
{
  free_logic_state(state);
}

static int
test_require_impl(struct TestState *state)
{
  sl_LogicState *logic_state = prepare_test_require();
  int err = run_test_require(logic_state);
  cleanup_test_require(logic_state);
  if (err != 0)
    return err;
  return 0;
}

struct TestCase test_paths = { "Paths", &run_test_paths };
struct TestCase test_namespaces = { "Namespaces", &run_test_namespaces };
struct TestCase test_types = { "Types", &run_test_types };
struct TestCase test_values = { "Values", &run_test_values };
struct TestCase test_require = { "Require", &test_require_impl };
