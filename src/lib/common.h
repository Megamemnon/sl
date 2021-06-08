#ifndef COMMON_H
#define COMMON_H

#include <stdint.h>

extern int verbose;

/* Booleans */
typedef int bool;
#define TRUE 1
#define FALSE 0

/* Misc helpers */
#define PROPAGATE_ERROR(err) \
do { \
  if (err) \
    return err; \
} \
while(0)

/* Array helpers */
#include <stdlib.h>

struct DynamicArray
{
  void *data;

  size_t element_size;
  size_t length;
  size_t reserved;
};

typedef struct DynamicArray Array;

#define ARRAY_INIT(array, type) \
do { \
  array.data = malloc(sizeof(type)); \
  array.element_size = sizeof(type); \
  array.length = 0; \
  array.reserved = 1; \
} \
while(0)

#define ARRAY_INIT_WITH_RESERVED(array, type, to_reserve) \
do { \
  array.data = malloc(sizeof(type) * to_reserve); \
  array.element_size = sizeof(type); \
  array.length = 0; \
  array.reserved = to_reserve; \
} \
while(0)

#define ARRAY_LENGTH(array) array.length

#define ARRAY_GET(array, type, index) (&(((type *)array.data)[index]))

#define ARRAY_APPEND(array, type, item) \
do { \
  if (array.reserved < array.length + 1) \
  { \
    array.reserved = array.reserved * 2; \
    array.data = realloc(array.data, array.element_size * array.reserved); \
  } \
  ((type *)array.data)[array.length] = item; \
  array.length += 1; \
} \
while(0)

#define ARRAY_POP(array) \
do { \
  array.length -= 1; \
} \
while(0)

#define ARRAY_FREE(array) \
do { \
  free(array.data); \
  array.element_size = 0; \
  array.length = 0; \
  array.reserved = 0; \
} \
while(0)

#define ARRAY_COPY(dst, src) \
do { \
  dst.length = src.length; \
  dst.element_size = src.element_size; \
  dst.reserved = src.reserved; \
  dst.data = malloc(src.element_size * src.reserved); \
  memcpy(dst.data, src.data, src.element_size * src.length); \
} \
while(0)

#endif
