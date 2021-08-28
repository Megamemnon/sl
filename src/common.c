#include "common.h"
#include <string.h>

#define SL_COPY_FILE_BUFFER_SIZE 4096

int sl_copy_file(const char *dst_path, const char *src_path)
{
  FILE *dst, *src;
  unsigned char buf[SL_COPY_FILE_BUFFER_SIZE];
  dst = fopen(dst_path, "w");
  if (dst == NULL)
    return 1;
  src = fopen(src_path, "r");
  if (src == NULL) {
    fclose(dst);
    return 2;
  }
  while (1) {
    size_t read, written;
    read = fread(buf, 1, SL_COPY_FILE_BUFFER_SIZE, src);
    if (read == 0) /* TODO: check for errors. */
      break;
    written = fwrite(buf, 1, read, dst);
    if (written != read) {
      fclose(dst);
      fclose(src);
      return 2;
    }
  }
  fclose(dst);
  fclose(src);
  return 0;
}

int
strslicecmp(const struct sl_StringSlice a, const struct sl_StringSlice b)
{
  if (a.length > b.length)
    return 1;
  if (b.length > a.length)
    return -1;
  return strncmp(a.begin, b.begin, a.length);
}

int
strslicecmp2(const struct sl_StringSlice a, const char *b)
{
  if (a.length > strlen(b))
    return 1;
  if (strlen(b) > a.length)
    return -1;
  return strncmp(a.begin, b, a.length);
}

char *
slice_to_string(struct sl_StringSlice slice)
{
  char *str = malloc(slice.length + 1);
  if (str == NULL)
    return NULL;
  strncpy(str, slice.begin, slice.length);
  str[slice.length] = '\0';
  return str;
}

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
