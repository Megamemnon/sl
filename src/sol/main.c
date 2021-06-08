#include "sol.h"

#include <arg.h>
#include <stdio.h>

int verbose = 1;

int
main(int argc, char **argv)
{
  struct CommandLine cl;
  cl.argc = argc;
  cl.argv = argv;

  int err = sol_verify("examples/zfc.sol");

  printf("result: %s\n", err ? "invalid" : "valid");

  return 0;
}
