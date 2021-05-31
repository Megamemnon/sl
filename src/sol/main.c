#include <common.h>

#include "sol.h"

#include <stdio.h>

int verbose = 1;

int
main(int argc, char **argv)
{
  int err = sol_verify("examples/zfc.sol");

  printf("result: %s\n", err ? "invalid" : "valid");

  return 0;
}
