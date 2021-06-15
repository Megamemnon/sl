#include "arg.h"
#include <string.h>

int
parse_command_line(struct CommandLine *cl)
{
  /* Iterate through the command line arguments. */
  bool arguments_only = FALSE;
  for (size_t i = 0; i < cl->argc; ++i)
  {
    const char *arg = cl->argv[i];
    if (!arguments_only)
    {
      /* We are still parsing options. */
      if (strcmp(arg, "--") == 0)
      {
        arguments_only = TRUE;
      }

      /* We can assume that `strlen(arg) > 0`. */
      if (arg[0] == '-')
      {
        if (strlen(arg) == 1)
        {
          /* TODO: error. */
          return 1;
        }

        if (arg[1] == '-')
        {
          /* Here we have a long-form argument. */
        }
        else
        {
          /* Short form. */
        }
      }
      else
      {
        /* Add this as an argument. */
      }
    }
    else
    {
      /* Just add this argument to the list of true arguments. */
    }
  }

  /* Verify that all required arguments are filled out. */
  for (size_t i = 0; i < ARRAY_LENGTH(cl->options); ++i)
  {

  }

  return 0;
}

void
free_command_line(struct CommandLine *cl)
{
  ARRAY_FREE(cl->arguments);
}
