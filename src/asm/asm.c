#include "asm.h"

#include <string.h>

const char *asm_keywords[] = {
  "section",
  "global"
};
const char *asm_symbols[] = {
  ".",
  ":",
  ";",
  "$",
  "-",
  "//"
};
