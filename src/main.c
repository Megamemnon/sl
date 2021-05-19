#include "lang.h"
#include "common.h"

#include "asm-lang.h"
#include "c-lang.h"

int verbose = 1;

int
main(int argc, char **argv)
{
  struct LanguageSpec asm_lang = get_asm_spec();

  compile("examples/hello_world.asm", &asm_lang);

  return 0;
}
