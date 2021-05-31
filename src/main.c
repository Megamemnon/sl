#include "lang.h"
#include "common.h"

#include "asm-lang.h"
#include "c-lang.h"
#include "sol-lang.h"

#include <stdio.h>

int verbose = 1;

int
main(int argc, char **argv)
{
  /*struct LanguageSpec sol_lang = get_sol_spec();

  compile("examples/zfc.sol", &sol_lang);*/

  int err = sol_verify("examples/zfc.sol");

  printf("result: %s\n", err ? "invalid" : "valid");

  return 0;
}
