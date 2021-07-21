#include "test_case.h"

int
main(int argc, char **argv)
{
  struct TestState state;
  init_test_state(&state);

  run_test_case(&state, test_values);

  cleanup_test_state(&state);
  return 0;
}

void
init_test_state(struct TestState *state)
{

}

void
run_test_case(struct TestState *state, run_test_t test_case)
{
  int result = test_case(state);
}

void
cleanup_test_state(struct TestState *state)
{

}
