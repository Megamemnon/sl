#ifndef TEST_CASE_H
#define TEST_CASE_H

struct TestCase
{
  void (clean_up *)(void *userdata);
};

#endif
