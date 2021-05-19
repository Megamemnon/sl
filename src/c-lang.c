#include "c-lang.h"

#include <string.h>

const char *c_keywords[] = {
  "break",
  "case",
  "char",
  "const",
  "continue",
  "default",
  "do",
  "double",
  "else",
  "enum",
  "extern",
  "float",
  "for",
  "if",
  "int",
  "long",
  "return",
  "short",
  "sizeof",
  "static",
  "struct",
  "switch",
  "typedef",
  "unsigned",
  "void",
  "while"
};
//const char *c_separators = "()[]{}<>,;&|%+-=#/'\"?:! *\t\n";

struct ParseSpec
get_c_parse_spec()
{
  struct ParseSpec spec = {};

  spec.keywords = c_keywords;
  spec.keywords_n = sizeof(c_keywords) / sizeof(c_keywords[0]);

  //spec.separators = c_separators;
  //spec.separators_n = strlen(c_separators);
  spec.symbols = NULL;
  spec.symbols_n = 0;

  return spec;
}

struct LanguageSpec
get_c_spec()
{
  struct LanguageSpec spec = {};
  spec.get_parse = &get_c_parse_spec;
  return spec;
}
