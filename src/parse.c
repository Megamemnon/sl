#include "parse.h"
#include "common.h"

#include <stdio.h>

void
parse_file(const char *file_path)
{
  if (verbose >= 1)
    printf("Parsing file '%s'\n", file_path);

  FILE *file = fopen(file_path, "r");
  if (file == NULL)
  {
    printf("Could not open file '%s'\n", file_path);
    return;
  }

  char line_buf[4096];
  while (fgets(line_buf, 4096, file) != NULL)
  {
    tokenize_line(line_buf);
  }

  fclose(file);
}

void
tokenize_line(const char *line)
{
  for (const char *c = line; *c != '\0'; ++c)
  {

  }
}
