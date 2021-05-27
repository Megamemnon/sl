#ifndef LANG_H
#define LANG_H

#include "lex.h"

typedef struct LexSpec (* get_lex_spec_t)();

struct LanguageSpec
{
  get_lex_spec_t get_parse;
};

struct ParseSpec
get_language_parse_spec(const struct LanguageSpec *lang);

void
compile(const char *file_path, const struct LanguageSpec *lang);

#endif
