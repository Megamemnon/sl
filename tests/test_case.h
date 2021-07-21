#ifndef TEST_CASE_H
#define TEST_CASE_H

struct TestState
{

};

typedef int (* run_test_t)(struct TestState *);

/* Methods for running tests. */
void
init_test_state(struct TestState *state);

void
run_test_case(struct TestState *state, run_test_t test_case);

void
cleanup_test_state(struct TestState *state);

/* Test cases for core logic. */
extern run_test_t test_values;

#endif
