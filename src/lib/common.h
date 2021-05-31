#ifndef COMMON_H
#define COMMON_H

#include <stdint.h>

extern int verbose;

/* Misc helpers */
#define PROPAGATE_ERROR(err) \
do { \
  if (err) \
    return err; \
} \
while(0)

/* Array helpers */
#define ARRAY_INIT(array, array_len) \
do { \
  array = malloc(sizeof(*array)); \
  array_len = 0; \
} \
while(0)

#define ARRAY_INIT_WITH_SIZE(array, array_len, size) \
do { \
  array = malloc(sizeof(*array) * size); \
  array_len = size; \
} \
while(0)

#define ARRAY_APPEND(item, array, array_len) \
do { \
  array_len += 1; \
  array = realloc(array, sizeof(*array) * array_len); \
  array[array_len - 1] = item; \
} \
while(0)

#define ARRAY_FREE(array, array_len) \
do { \
  free(array); \
  array = NULL; \
  array_len = 0; \
} \
while(0)

#define ARRAY_COPY(dst_array, dst_len, src_array, src_len) \
do { \
  dst_len = src_len; \
  dst_array = malloc(sizeof(*dst_array) * dst_len); \
  memcpy(dst_array, src_array, sizeof(*dst_array) * dst_len); \
} \
while(0)

#endif
