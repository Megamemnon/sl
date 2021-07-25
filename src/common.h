#ifndef COMMON_H
#define COMMON_H

#include <stdint.h>
#include <stdarg.h>

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

#include <stdlib.h>
/* Memory helpers */
#define SL_NEW(type) malloc(sizeof(type))
#define SL_FREE(ptr) free(ptr)

/* Array helpers */
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
  (array).data = malloc(sizeof(type)); \
  (array).element_size = sizeof(type); \
  (array).length = 0; \
  (array).reserved = 1; \
} \
while (0)

#define ARRAY_INIT_WITH_RESERVED(array, type, to_reserve) \
do { \
  (array).data = malloc(sizeof(type) * to_reserve); \
  (array).element_size = sizeof(type); \
  (array).length = 0; \
  (array).reserved = to_reserve; \
} \
while (0)

#define ARRAY_LENGTH(array) (array).length

#define ARRAY_GET(array, type, index) (&(((type *)(array).data)[index]))

#define ARRAY_APPEND(array, type, item) \
do { \
  if ((array).reserved < (array).length + 1) \
  { \
    (array).reserved = (array).reserved * 2; \
    (array).data = realloc((array).data, (array).element_size * (array).reserved); \
  } \
  ((type *)(array).data)[(array).length] = item; \
  (array).length += 1; \
} \
while (0)

#define ARRAY_POP(array) \
do { \
  (array).length -= 1; \
} \
while (0)

#define ARRAY_FREE(array) \
do { \
  free((array).data); \
  (array).element_size = 0; \
  (array).length = 0; \
  (array).reserved = 0; \
} \
while (0)

#define ARRAY_COPY(dst, src) \
do { \
  (dst).length = (src).length; \
  (dst).element_size = (src).element_size; \
  (dst).reserved = (src).reserved; \
  (dst).data = malloc((src).element_size * (src).reserved); \
  memcpy((dst).data, (src).data, (src).element_size * (src).length); \
} \
while (0)

#define MANAGED_ARRAY(type) \
struct \
{ \
  type *data; \
  size_t length; \
  size_t reserved; \
}

#define MANAGED_ARRAY_INIT(array) \
do { \
  (array).data = malloc(sizeof(*(array).data)); \
  (array).length = 0; \
  (array).reserved = 1; \
} \
while (0)

#define MANAGED_ARRAY_LENGTH(array) (array).length

#define MANAGED_ARRAY_GET(array, index) &((array).data[index])

#define MANAGED_ARRAY_APPEND(array, item) \
do { \
  if ((array).reserved < (array).length + 1) \
  { \
    (array).reserved = (array).reserved * 2; \
    (array).data = realloc((array).data, sizeof(*(array).data) * (array).reserved); \
  } \
  (array).data[(array).length] = item; \
  (array).length += 1; \
} \
while (0)

#define MANAGED_ARRAY_POP(array) \
do { \
  (array).length -= 1; \
} \
while (0)

#define MANAGED_ARRAY_FREE(array) \
do { \
  free((array).data); \
  (array).length = 0; \
  (array).reserved = 0; \
} \
while (0)

#define ARR(type) MANAGED_ARRAY(type)
#define ARR_INIT(array) MANAGED_ARRAY_INIT(array)
#define ARR_LENGTH(array) MANAGED_ARRAY_LENGTH(array)
#define ARR_GET(array, index) MANAGED_ARRAY_GET(array, index)
#define ARR_APPEND(array, item) MANAGED_ARRAY_APPEND(array, item)
#define ARR_POP(array) MANAGED_ARRAY_POP(array)
#define ARR_FREE(array) MANAGED_ARRAY_FREE(array)

/* String helpers. */
struct sl_StringSlice
{
  const char *begin;
  size_t length;
};

uint32_t
hash(char *str);

char *
strndup(const char *str, size_t n);

int
asprintf(char **str, const char *fmt, ...);

int
vasprintf(char **str, const char *fmt, va_list vlist);

#endif
