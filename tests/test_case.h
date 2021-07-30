#ifndef TEST_CASE_H
#define TEST_CASE_H

/* State for managing tests. */
struct TestState
{
  int error;
};

typedef int (* run_test_t)(struct TestState *);
struct TestCase
{
  const char *name;
  run_test_t run;
};

/* Methods for running tests. */
void
init_test_state(struct TestState *state);

void
run_test_case(struct TestState *state, struct TestCase test_case);

void
cleanup_test_state(struct TestState *state);

/* Test cases for core logic. */
extern struct TestCase test_types;
extern struct TestCase test_values;
extern struct TestCase test_require;

/* Test cases for parsing. */
extern struct TestCase test_input;
extern struct TestCase test_lexer;
extern struct TestCase test_parser;

#endif
