#include "common.h"

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
