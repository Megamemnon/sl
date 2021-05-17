#ifndef PARSE_H
#define PARSE_H

#include <stdlib.h>

struct ParseSpec
{
  const char *keywords;
  size_t keywords_n;
};

struct Token
{
  unsigned int id;
  const char *value;
};

void
parse_file(const char *file_path);

void
tokenize_line(const char *line);

#endif
