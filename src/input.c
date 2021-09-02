#include "parse.h"
#include <string.h>

#define MSG_VIEW_SIZE 256

struct sl_TextInput {
  void *data;

  void (* free_data)(void *);
  bool (* at_end)(void *);
  char * (* gets)(char *, size_t, void *);
  void (* get_line)(char *, size_t, size_t, void *);
};

struct sl_TextInputLineBuffer {
  char *main_buffer;
  size_t main_buffer_size;
  char *overflow_buffer;
  char *active_buffer;
};

bool
sl_input_at_end(sl_TextInput *input)
{
  if (input == NULL)
    return TRUE;
  if (input->at_end == NULL)
    return TRUE;
  return input->at_end(input->data);
}

char *
sl_input_gets(char *dst, size_t n, sl_TextInput *input)
{
  if (input == NULL)
    return NULL;
  if (input->at_end == NULL)
    return NULL;
  return input->gets(dst, n, input->data);
}

sl_TextInputLineBuffer *
sl_input_make_line_buffer(size_t main_buffer_size)
{
  sl_TextInputLineBuffer *buf;
  buf = SL_NEW(sl_TextInputLineBuffer);
  if (buf == NULL)
    return NULL;
  buf->main_buffer = malloc(main_buffer_size);
  if (buf->main_buffer == NULL) {
    free(buf);
    return NULL;
  }
  buf->main_buffer_size = main_buffer_size;
  buf->overflow_buffer = NULL;
  buf->active_buffer = NULL;
  return buf;
}

void
sl_input_free_line_buffer(sl_TextInputLineBuffer *buffer)
{
  if (buffer == NULL)
    return;
  if (buffer->main_buffer != NULL)
    free(buffer->main_buffer);
  if (buffer->overflow_buffer != NULL)
    free(buffer->overflow_buffer);
  free(buffer);
}

const char *
sl_input_get_line_buffer_contents(sl_TextInputLineBuffer *buffer)
{
  return buffer->active_buffer;
}

int
sl_input_get_line(sl_TextInput *input, sl_TextInputLineBuffer *buffer)
{
  char *result;
  if (buffer->overflow_buffer != NULL)
    free(buffer->overflow_buffer);
  if (sl_input_at_end(input)) {
    buffer->active_buffer = NULL;
    return 0;
  }
  result = sl_input_gets(buffer->main_buffer, buffer->main_buffer_size, input);
  if (result == NULL) {
    buffer->active_buffer = NULL;
    return 1;
  }

  /* If the result doesn't end in a newline, copy this into the overflow
     buffer and keep consuming until we get to a newline. */
  if (buffer->main_buffer[strlen(buffer->main_buffer) - 1] != '\n') {
    buffer->overflow_buffer = strdup(buffer->main_buffer);
    if (buffer->overflow_buffer == NULL) {
      buffer->active_buffer = NULL;
      return 1;
    }
    do {
      char *reallocated;
      result = sl_input_gets(buffer->main_buffer, buffer->main_buffer_size,
          input);
      if (result == NULL) {
        free(buffer->overflow_buffer);
        buffer->overflow_buffer = NULL;
        return 1;
      }
      reallocated = realloc(buffer->overflow_buffer,
          strlen(buffer->main_buffer) + strlen(buffer->overflow_buffer) + 1);
      if (reallocated == NULL) {
        free(buffer->overflow_buffer);
        buffer->active_buffer = NULL;
        return 1;
      }
      buffer->overflow_buffer = reallocated;
      strcat(buffer->overflow_buffer, buffer->main_buffer);
    } while (buffer->overflow_buffer[strlen(buffer->overflow_buffer) - 1]
        != '\n');
    buffer->active_buffer = buffer->overflow_buffer;
  } else {
    buffer->active_buffer = buffer->main_buffer;
  }
  return 0;
}

/* --- File Input --- */
static void
file_free(void *data)
{
  FILE *f = (FILE *)data;
  fclose(f);
}

static bool
file_at_end(void *data)
{
  FILE *f = (FILE *)data;
  if (feof(f) == 0)
    return FALSE;
  return TRUE;
}

static char *
file_gets(char *dst, size_t n, void *data)
{
  FILE *f = (FILE *)data;
  return fgets(dst, n, f);
}

static void
file_get_line(char *dst, size_t dst_len, size_t line, void *data)
{
  FILE *f;
  long tmp_pos;
  char buf[MSG_VIEW_SIZE];

  f = (FILE *)data;
  tmp_pos = ftell(f);

  fseek(f, 0, SEEK_SET);
  for (size_t i = 0; i < line; ++i)
  {
    do {
      char *result = fgets(buf, MSG_VIEW_SIZE, f);
      if (result == NULL)
      {
        fseek(f, tmp_pos, SEEK_SET);
        return;
      }
    } while (buf[strlen(buf) - 1] != '\n');
  }
  fgets(dst, dst_len, f);
  fseek(f, tmp_pos, SEEK_SET);
}

sl_TextInput *
sl_input_from_file(const char *file_path)
{
  if (file_path == NULL)
    return NULL;
  sl_TextInput *input = SL_NEW(sl_TextInput);
  if (input == NULL)
    return NULL;
  FILE *f = fopen(file_path, "r");
  if (f == NULL)
  {
    free(input);
    return NULL;
  }
  input->data = f;
  input->free_data = &file_free;
  input->at_end = &file_at_end;
  input->gets = &file_gets;
  input->get_line = &file_get_line;
  return input;
}

/* --- String Input --- */
struct StringInputData
{
  const char *str;
  size_t at;
  bool reached_end;
};

static void
string_free(void *data)
{
  struct StringInputData *input = (struct StringInputData *)data;
  free(input);
}

static bool
string_at_end(void *data)
{
  struct StringInputData *input = (struct StringInputData *)data;
  if (input->reached_end)
    return TRUE;
  return input->reached_end;
}

static char *
string_gets(char *dst, size_t n, void *data)
{
  struct StringInputData *input = (struct StringInputData *)data;
  size_t end;
  char *result;
  if (input == NULL)
    return NULL;
  if (input->str[input->at] == '\0')
  {
    input->reached_end = TRUE;
    return NULL;
  }
  /* Iterate and try to find a line break in [at, at + n - 1]. */
  for (end = input->at; end < input->at + n; ++end)
  {
    if (input->str[end] == '\n')
      break;
    else if (input->str[end] == '\0')
      break;
  }
  /* Copy the data, add a NULL at the end, and then advance the pointer. */
  result = strncpy(dst, &input->str[input->at], end - input->at + 1);
  if (result != NULL)
    result[(end - input->at) + 1] = '\0';
  input->at += (end - input->at) + 1;
  return result;
}

static void
string_get_line(char *dst, size_t dst_len, size_t line, void *data)
{
  struct StringInputData *input;
  size_t tmp_pos;
  char buf[MSG_VIEW_SIZE];

  input = (struct StringInputData *)data;
  tmp_pos = input->at;

  input->at = 0;
  for (size_t i = 0; i < line; ++i)
  {
    do {
      char *result = string_gets(buf, MSG_VIEW_SIZE, data);
      if (result == NULL)
      {
        input->at = tmp_pos;
        return;
      }
    } while (buf[strlen(buf) - 1] != '\n');
  }
  string_gets(dst, dst_len, data);
  input->at = tmp_pos;
}

sl_TextInput *
sl_input_from_string(const char *string)
{
  if (string == NULL)
    return NULL;
  sl_TextInput *input = SL_NEW(sl_TextInput);
  if (input == NULL)
    return NULL;
  {
    struct StringInputData *string_data = SL_NEW(struct StringInputData);
    if (string_data == NULL)
    {
      free(input);
      return NULL;
    }
    string_data->str = string;
    string_data->at = 0;
    string_data->reached_end = FALSE;
    input->data = string_data;
  }
  input->free_data = &string_free;
  input->at_end = &string_at_end;
  input->gets = &string_gets;
  input->get_line = &string_get_line;
  return input;
}

/* --- Generic Methods --- */
void
sl_input_free(sl_TextInput *input)
{
  if (input == NULL)
    return;
  if (input->free_data != NULL)
    input->free_data(input->data);
  free(input);
}

void
sl_input_show_message(sl_TextInput *input, size_t line, size_t column,
  const char *message, sl_MessageType type)
{
  char buf[MSG_VIEW_SIZE];

  if (input == NULL)
    return;
  if (input->get_line == NULL)
    return;

  input->get_line(buf, MSG_VIEW_SIZE, line, input->data);
  printf("Error at (%zu, %zu): %s\n", line, column, message);
  printf("\t%s", buf);
  printf("\t");
  for (size_t i = 0; i < column; ++i)
    printf(" ");
  printf("^");
  printf("\n\n");
}
