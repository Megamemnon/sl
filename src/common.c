#include "common.h"
#include <stdio.h>

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
sl_vasprintf(const char *format, va_list vlist)
{
  va_list vlist_copy;
  va_copy(vlist_copy, vlist);
  int len = vsnprintf(NULL, 0, format, vlist_copy) + 1;
  va_end(vlist_copy);
  char *str = malloc(len);
  vsnprintf(str, len, format, vlist);
  str[len] = '\0';
  return str;
}

char *
sl_asprintf(const char *format, ...)
{
  va_list vlist;
  va_start(vlist, format);
  char *str = sl_vasprintf(format, vlist);
  va_end(vlist);
  return str;
}
