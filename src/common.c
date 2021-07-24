#include "common.h"
#include <stdio.h>
#include <string.h>

/* From http://www.cse.yorku.ca/~oz/hash.html */
uint32_t
hash(char *str)
{
  uint32_t hash = 5381;
  int c;

  while (c = *str++)
    hash = ((hash << 5) + hash) + c; /* hash * 33 + c */

  return hash;
}

char *
strndup(const char *str, size_t n)
{
  if (strlen(str) <= n)
  {
    return strdup(str);
  }
  else
  {
    char *result = malloc(n + 1);
    if (result == NULL)
      return NULL;
    strncpy(result, str, n);
    result[n] = '\0';
    return result;
  }
}

int
asprintf(char **str, const char *fmt, ...)
{
  va_list args;
  va_start(args, fmt);
  int result = vasprintf(str, fmt, args);
  va_end(args);
  return result;
}

int
vasprintf(char **str, const char *fmt, va_list vlist)
{
  va_list vlist_copy;
  va_copy(vlist_copy, vlist);
  int result = vsnprintf(NULL, 0, fmt, vlist_copy);
  va_end(vlist_copy);
  if (result < 0)
    return result;
  *str = malloc(result + 1);
  result = vsprintf(*str, fmt, vlist);
  return result;
}
