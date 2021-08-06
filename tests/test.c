#include "test_case.h"
#include <ctype.h>
#include <stdio.h>

int
main(int argc, char **argv)
{
  struct TestCase test_cases[] = {
    test_paths,
    test_namespaces,
    test_types,
    test_constants,
    test_values,
    test_require,

    test_input,
    test_lexer,
    test_parser
  };

  struct TestState state;
  init_test_state(&state);

  for (size_t i = 0; i < sizeof(test_cases) / sizeof(struct TestCase); ++i)
  {
    run_test_case(&state, test_cases[i]);
    if (state.error != 0)
      break;
  }

  cleanup_test_state(&state);
  return state.error;
}

void
init_test_state(struct TestState *state)
{
  state->error = 0;
}

void
run_test_case(struct TestState *state, struct TestCase test_case)
{
  printf("Running test \"%s\"...", test_case.name);
  state->error = test_case.run(state);
  if (state->error == 0)
    printf(" Good.\n");
  else
    printf(" Failed.\n");
}

void
cleanup_test_state(struct TestState *state)
{

}
