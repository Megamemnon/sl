#include "arg.h"
#include <string.h>

/* TODO: add a method to verify the list of options given to the
   parser by checking strings are alphanumeric, etc.? */

static struct CommandLineOption *
lookup_by_long_name(const char *name, struct CommandLine *cl)
{
  for (size_t i = 0; i < ARRAY_LENGTH(cl->options); ++i)
  {
    struct CommandLineOption *opt = *ARRAY_GET(cl->options,
      struct CommandLineOption *, i);
    if (opt->long_name != NULL)
    {
      if (strcmp(opt->long_name, name) == 0)
        return opt;
    }
  }
  return NULL;
}

static struct CommandLineOption *
lookup_by_short_name(char c, struct CommandLine *cl)
{
  for (size_t i = 0; i < ARRAY_LENGTH(cl->options); ++i)
  {
    struct CommandLineOption *opt = *ARRAY_GET(cl->options,
      struct CommandLineOption *, i);
    if (opt->short_name == c)
      return opt;
  }
  return NULL;
}

static int
parse_long_form(int current_arg, struct CommandLine *cl)
{
  const char *options = cl->argv[current_arg];
  if (strlen(options) < 3)
    return 1;
  if (options[0] != '-' || options[1] != '-')
    return 1;
  const char *arg = &options[2];
  const char *value = NULL;
  size_t arg_length = 0;
  for (const char *c = &options[2]; *c != '\0'; ++c)
  {
    if (*c == '=')
    {
      /* Check that we still have another character to go. */
      if (c[1] == '\0')
        return 1;
      value = &c[1];
      arg_length = c - arg;
      break;
    }
  }
  if (value == NULL)
    arg_length = strlen(arg);
  char *arg_temp = malloc(arg_length + 1);
  strncpy(arg_temp, arg, arg_length);
  arg_temp[arg_length] = '\0';
  struct CommandLineOption *opt = lookup_by_long_name(arg_temp, cl);
  free(arg_temp);
  if (opt == NULL)
    return 1;
  opt->present = TRUE;
  if (opt->takes_argument)
  {
    if (value == NULL)
      return 1;
    opt->argument = strdup(value);
    return 0;
  }
  else
  {
    if (value != NULL)
      return 1;
    return 0;
  }
}

/* Return the number of extra arguments consumed (-1 on error,
   otherwise 0 or 1). */
static int
parse_short_form(int current_arg, struct CommandLine *cl)
{
  const char *options = cl->argv[current_arg];
  if (strlen(options) < 2)
    return -1;
  if (options[0] != '-')
    return -1;
  for (const char *c = &options[1]; *c != '\0'; ++c)
  {
    /* Look up the option pointed to by *c. */
    struct CommandLineOption *opt = lookup_by_short_name(*c, cl);
    if (opt == NULL)
      return -1;
    opt->present = TRUE;
    if (opt->takes_argument)
    {
      /* If it takes an argument, expect an argument. */
      /* Is this the last character? Then consume the next token as
         the argument. */
      if (strlen(c) == 1)
      {
        if (current_arg + 1 >= cl->argc)
          return -1;
        opt->argument = strdup(cl->argv[current_arg + 1]);
        return 1;
      }
      else
      {
        opt->argument = strdup(&c[1]);
        return 0;
      }
    }
  }
  return 0;
}

static int
add_argument(int current_arg, struct CommandLine *cl)
{
  char *arg = strdup(cl->argv[current_arg]);
  ARRAY_APPEND(cl->arguments, char *, arg);
}

void
init_command_line(struct CommandLine *cl, int argc, char * const *argv)
{
  cl->argc = argc;
  cl->argv = argv;
  ARRAY_INIT(cl->options, struct CommandLineOption *);
  ARRAY_INIT(cl->arguments, char *);
}

void
add_command_line_option(struct CommandLine *cl, struct CommandLineOption *opt)
{
  ARRAY_APPEND(cl->options, struct CommandLineOption *, opt);
}

int
parse_command_line(struct CommandLine *cl)
{
  /* Iterate through the command line arguments. */
  bool arguments_only = FALSE;
  for (size_t i = 1; i < cl->argc; ++i)
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
          /* We have a long-form argument. */
          int err = parse_long_form(i, cl);
          if (err)
            return 1;
        }
        else
        {
          /* Short form. */
          int advance = parse_short_form(i, cl);
          if (advance == -1)
            return 1;
          i += advance;
        }
      }
      else
      {
        /* Add this as an argument. */
        char *argument = strdup(arg);
        ARRAY_APPEND(cl->arguments, char *, argument);
      }
    }
    else
    {
      /* Just add this argument to the list of true arguments. */
      char *argument = strdup(arg);
      ARRAY_APPEND(cl->arguments, char *, argument);
    }
  }

  /* Fill in the default arguments if they do not override user arguments. */
  for (size_t i = 0; i < ARRAY_LENGTH(cl->options); ++i)
  {
    struct CommandLineOption *opt = *ARRAY_GET(cl->options,
      struct CommandLineOption *, i);
    if (opt->default_argument != NULL && opt->argument == NULL)
      opt->argument = strdup(opt->default_argument);
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
  for (size_t i = 0; i < ARRAY_LENGTH(cl->options); ++i)
  {
    struct CommandLineOption *opt = *ARRAY_GET(cl->options,
      struct CommandLineOption *, i);
    if (opt->argument != NULL)
      free(opt->argument);
  }
  ARRAY_FREE(cl->options);

  for (size_t i = 0; i < ARRAY_LENGTH(cl->arguments); ++i)
  {
    char *arg = *ARRAY_GET(cl->arguments, char *, i);
    free(arg);
  }
  ARRAY_FREE(cl->arguments);
}
