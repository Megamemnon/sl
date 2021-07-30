#include "test_case.h"
#include <logic.h>
#include <core.h>

static int
run_test_types(struct TestState *state)
{
  sl_LogicState *logic;
  logic = new_logic_state(NULL);

  {
    sl_SymbolPath *path = init_symbol_path();
    push_symbol_path(path, "type1");
    if (add_type(logic, path, FALSE, FALSE) != sl_LogicError_None)
      return 1;
    if (add_type(logic, path, FALSE, FALSE)
      != sl_LogicError_SymbolAlreadyExists)
      return 1;
    free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = init_symbol_path();
    push_symbol_path(path, "type2");
    if (add_type(logic, path, TRUE, FALSE) != sl_LogicError_None)
      return 1;
    free_symbol_path(path);
  }

  {
    sl_SymbolPath *path = init_symbol_path();
    push_symbol_path(path, "type3");
    if (add_type(logic, path, FALSE, TRUE)
      != sl_LogicError_CannotBindNonAtomic)
      return 1;
    if (add_type(logic, path, TRUE, TRUE) != sl_LogicError_None)
      return 1;
    free_symbol_path(path);
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

struct TestCase test_types = { "Types", &run_test_types };
struct TestCase test_values = { "Values", &run_test_values };
struct TestCase test_require = { "Require", &test_require_impl };
