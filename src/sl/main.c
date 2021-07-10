#include "sl.h"

#include <arg.h>
#include <stdio.h>

struct CommandLineOption version_opt = {
  .short_name = 'v',
  .long_name = "version",
  .takes_argument = FALSE
};
struct CommandLineOption help_opt = {
  .short_name = 'h',
  .long_name = "help",
  .takes_argument = FALSE
};
struct CommandLineOption verbose_opt = {
  .short_name = 'V',
  .long_name = "verbose",
  .takes_argument = FALSE
};
struct CommandLineOption out_opt = {
  .short_name = 'o',
  .long_name = "out",
  .takes_argument = TRUE
};

static void
print_version()
{
  printf("version 0.0.1\n");
}

static void
print_help()
{
  printf("help\n");
}

int
main(int argc, char **argv)
{
  struct CommandLine cl;
  init_command_line(&cl, argc, argv);

  add_command_line_option(&cl, &version_opt);
  add_command_line_option(&cl, &help_opt);
  add_command_line_option(&cl, &verbose_opt);
  add_command_line_option(&cl, &out_opt);

  parse_command_line(&cl);

  if (version_opt.present)
  {
    print_version();
    free_command_line(&cl);
    return 0;
  }

  if (help_opt.present)
  {
    print_help();
    free_command_line(&cl);
    return 0;
  }

  if (verbose_opt.present)
    verbose = 1;
  else
    verbose = 0;

  FILE *output = stdout;
  if (out_opt.argument != NULL)
  {
    output = fopen(out_opt.argument, "w");
    if (output == NULL)
    {
      /* TODO: error, can't open file for write. */
      free_command_line(&cl);
      return 1;
    }
  }

  for (size_t i = 0; i < ARRAY_LENGTH(cl.arguments); ++i)
  {
    const char *path = *ARRAY_GET(cl.arguments, char *, i);
    sl_verify(path, output);
  }

  if (out_opt.argument != NULL)
  {
    fclose(output);
  }

  free_command_line(&cl);

  return 0;
}
