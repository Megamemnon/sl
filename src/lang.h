#ifndef LANG_H
#define LANG_H

#include "lex.h"

struct LanguageSpec
{

};

void
compile(const char *file_path, const struct LanguageSpec *lang);

#endif
