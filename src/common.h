#ifndef COMMON_H
#define COMMON_H

/* Array helpers */
#define ARRAY_INIT(array, array_len) \
  array = malloc(sizeof(*array)); \
  array_len = 0;

#define ARRAY_APPEND(item, array, array_len) \
  array_len += 1; \
  array = realloc(array, sizeof(*array) * array_len); \
  array[array_len - 1] = item;

#define ARRAY_FREE(array, array_len) \
  free(array); \
  array = NULL; \
  array_len = 0;

extern int verbose;

#endif
