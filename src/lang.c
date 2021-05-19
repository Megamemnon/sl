#include "lang.h"

struct ParseSpec
get_language_parse_spec(const struct LanguageSpec *lang)
{
  return lang->get_parse();
}

void
compile(const char *file_path, const struct LanguageSpec *lang)
{
  struct ParseSpec parse = get_language_parse_spec(lang);
  parse_file(file_path, &parse);
}
