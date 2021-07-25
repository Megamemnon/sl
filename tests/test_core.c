#include "test_case.h"
#include <logic.h>
#include <core.h>

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

struct TestCase test_values = { "Values", &run_test_values };
struct TestCase test_require = { "Require", &test_require_impl };
