#include "logic.h"
#include "core.h"
#include <string.h>

#define CURRENT_INTERCHANGE_VERSION 0

#define PUTC_AND_PROPAGATE_ERROR(c, f) \
do { \
  if ((c) != fputc((c), (f))) \
    return 1; \
} while (0);

static int write_uint32_t(uint32_t x, FILE *f)
{
  /* Little Endian. */
  uint32_t tmp;
  tmp = x;
  for (size_t i = 0; i < 4; ++i) {
    unsigned char byte = tmp & 0xFF;
    PUTC_AND_PROPAGATE_ERROR(byte, f);
    tmp = tmp >> 8;
  }
  return 0;
}

static size_t get_symbol_path_storage_size(const sl_SymbolPath *path)
{
  /* 4 bytes for the number of segments, and then 4 bytes for each segment. */
  return 4 * (1 + ARR_LENGTH(path->segments));
}

static size_t get_value_storage_size(const Value *value)
{
  return 4;
}

static size_t get_symbol_storage_size(const sl_LogicSymbol *sym)
{
  switch (sym->type) {
    case sl_LogicSymbolType_Namespace:
      return get_symbol_path_storage_size(sym->path);
      break;
    case sl_LogicSymbolType_Type:
      /* The size of the path, and a byte for flags. */
      return get_symbol_path_storage_size(sym->path) + 1;
      break;
    case sl_LogicSymbolType_Constant:
      /* The size of the path, and 4 bytes for the type id. */
      return get_symbol_path_storage_size(sym->path) + 4;
      break;
    case sl_LogicSymbolType_Constspace:
      /* The size of the path, and 4 bytes for the type id. */
      return get_symbol_path_storage_size(sym->path) + 4;
      break;
    case sl_LogicSymbolType_Expression:
      /* The size of the path, type, parameters, and replacement. */
      {
        const struct Expression *expr;
        size_t size;
        expr = (struct Expression *)sym->object;
        size = get_symbol_path_storage_size(sym->path);
        size += 4; /* Type ID */
        size += 8 * ARR_LENGTH(expr->parameters);
        size += 1; /* Flags. */
        if (expr->replace_with == NULL) {
          size += get_value_storage_size(expr->replace_with);
        }
        return size;
      }
      break;
    default:
      return 4;
      break;
  }
}

static int write_interchange_header(const sl_LogicState *state, FILE *f)
{
  int err;
  size_t header_len;
  size_t offset;

  /* Compute the header length. */
  header_len = 0;
  header_len += 8; /* Magic number and version number. */
  header_len += 4; /* String count. */
  header_len += 4 * ARR_LENGTH(state->string_table); /* String offsets. */
  header_len += 4; /* Symbol count. */
  header_len += 4 * ARR_LENGTH(state->symbol_table); /* Symbol offsets. */

  /* Magic number and version number. */
  PUTC_AND_PROPAGATE_ERROR('S', f);
  PUTC_AND_PROPAGATE_ERROR('L', f);
  PUTC_AND_PROPAGATE_ERROR('S', f);
  PUTC_AND_PROPAGATE_ERROR('L', f);
  err = write_uint32_t(CURRENT_INTERCHANGE_VERSION, f);
  PROPAGATE_ERROR(err);

  /* String table header. */
  err = write_uint32_t((uint32_t)ARR_LENGTH(state->string_table), f);
  PROPAGATE_ERROR(err);
  offset = header_len;
  for (size_t i = 0; i < ARR_LENGTH(state->string_table); ++i) {
    const char *str = *ARR_GET(state->string_table, i);
    err = write_uint32_t((uint32_t)offset, f);
    PROPAGATE_ERROR(err);
    offset += strlen(str) + 1;
  }

  /* Symbol table header. */
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i) {
    const sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    err = write_uint32_t((uint32_t)offset, f);
    PROPAGATE_ERROR(err);
    offset += get_symbol_storage_size(sym);
  }

  return 0;
}

static int write_string_table(const sl_LogicState *state, FILE *f)
{
  int err;
  for (size_t i = 0; i < ARR_LENGTH(state->string_table); ++i) {
    const char *str = *ARR_GET(state->string_table, i);
    err = fputs(str, f);
    if (err < 0)
      return err;
    PUTC_AND_PROPAGATE_ERROR('\0', f);
  }
  return 0;
}

static int write_path(const sl_SymbolPath *path, FILE *f)
{
  int err;
  err = write_uint32_t((uint32_t)ARR_LENGTH(path->segments), f);
  PROPAGATE_ERROR(err);
  for (size_t i = 0; i < ARR_LENGTH(path->segments); ++i) {
    uint32_t segment_string_id;
    segment_string_id = *ARR_GET(path->segments, i);
    err = write_uint32_t(segment_string_id, f);
    PROPAGATE_ERROR(err);
  }
  return 0;
}

#define TYPE_ATOMIC 0x01
#define TYPE_BINDS 0x02
#define TYPE_DUMMIES 0x04

static unsigned char get_type_flag_byte(const struct Type *type)
{
  unsigned char byte;
  byte = 0;
  if (type->atomic)
    byte |= TYPE_ATOMIC;
  if (type->binds)
    byte |= TYPE_BINDS;
  if (type->dummies)
    byte |= TYPE_DUMMIES;
}

static int write_type(const sl_LogicSymbol *sym, FILE *f)
{
  int err;
  unsigned char flags;
  err = write_path(sym->path, f);
  PROPAGATE_ERROR(err);
  flags = get_type_flag_byte((struct Type *)sym->object);
  PUTC_AND_PROPAGATE_ERROR(flags, f);
  return err;
}

static int write_constant(const sl_LogicSymbol *sym, FILE *f)
{
  int err;
  err = write_path(sym->path, f);
  PROPAGATE_ERROR(err);
  err = write_uint32_t(((struct Constant *)sym->object)->type_id, f);
  PROPAGATE_ERROR(err);
  return err;
}

static int write_constspace(const sl_LogicSymbol *sym, FILE *f)
{
  int err;
  err = write_path(sym->path, f);
  PROPAGATE_ERROR(err);
  err = write_uint32_t(((struct Constspace *)sym->object)->type_id, f);
  PROPAGATE_ERROR(err);
  return err;
}

static int write_expression(const sl_LogicSymbol *sym, FILE *f)
{
  int err;
  err = write_path(sym->path, f);
  PROPAGATE_ERROR(err);
  err = write_uint32_t(((struct Expression *)sym->object)->type_id, f);
  PROPAGATE_ERROR(err);
  return err;
}

static int write_symbol(const sl_LogicSymbol *sym, FILE *f)
{
  int err;
  switch (sym->type) {
    case sl_LogicSymbolType_Namespace:
      err = write_path(sym->path, f);
      break;
    case sl_LogicSymbolType_Type:
      err = write_type(sym, f);
      break;
    case sl_LogicSymbolType_Constant:
      err = write_constant(sym, f);
      break;
    case sl_LogicSymbolType_Constspace:
      err = write_constspace(sym, f);
      break;
    default:
      err = write_uint32_t(0xDEADBEEF, f);
      break;
  }
  PROPAGATE_ERROR(err);
  return 0;
}

static int write_symbol_table(const sl_LogicState *state, FILE *f)
{
  int err;
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i) {
    const sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    err = write_symbol(sym, f);
    PROPAGATE_ERROR(err);
  }
  return 0;
}

int sl_logic_state_write_to_interchange_file(const sl_LogicState *state,
    const char *file_path)
{
  FILE *f;
  int err;
  f = fopen(file_path, "w");
  if (f == NULL)
    return 1;
  err = write_interchange_header(state, f);
  PROPAGATE_ERROR(err); /* TODO: close `f` on error. */
  err = write_string_table(state, f);
  PROPAGATE_ERROR(err);
  err = write_symbol_table(state, f);
  PROPAGATE_ERROR(err);
  fclose(f);
  return 0;
}
