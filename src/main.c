#include "parse.h"
#include "common.h"

int verbose = 1;
#include <stdio.h>
int
main(int argc, char **argv)
{
  parse_file("examples/test.ma");

  return 0;
}
