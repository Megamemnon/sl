#ifndef ARG_H
#define ARG_H

#include "common.h"
/* A generic argument parser, derived from
   https://www.gnu.org/software/libc/manual/html_node/Argument-Syntax.html */
struct CommandLineOption
{
  char short_name;
  const char *long_name;

  bool takes_argument;
  const char *default_argument;

  bool present;
  char *argument;
};

struct CommandLine
{
  int argc;
  char * const *argv;

  Array options;
  Array arguments;
};

int
parse_command_line(struct CommandLine *cl);

void
free_command_line(struct CommandLine *cl);

#endif
