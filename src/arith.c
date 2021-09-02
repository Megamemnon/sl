#include "common.h"
#include <ctype.h>

/* --- Arbitrary Size Integer Arithmetic. */
struct sl_Natural {
  ARR(uint64_t) digits; /* Stored in NBO, so `digits[0]` is the most
                           significant digit, and so on. */
};

int sl_natural_from_string(const char *str, sl_Natural *nat)
{
  /* TODO: hex? */
  sl_Natural ten, digit, tmp;
  int err;

  err = sl_natural_from_uint64_t(0, nat);
  PROPAGATE_ERROR(err);
  err = sl_natural_from_uint64_t(10, &ten);
  PROPAGATE_ERROR(err);

  /* Make sure every character is a decimal digit. */
  for (const char *c = str; *c != '\0'; ++c) {
    if (!isdigit(*c))
      return 1;
  }

  /* Construct the value. */
  for (const char *c = str; *c != '\0'; ++c) {
    uint64_t digit_64;
    digit_64 = *c - '0';
    err = sl_natural_from_uint64_t(digit_64, &digit);
    PROPAGATE_ERROR(err);

    /* Multiply the number by ten, then add the next digit. */
    sl_natural_multiply(*nat, ten, &tmp);
    sl_natural_free(nat);
    sl_natural_copy(tmp, nat);
    sl_natural_free(&tmp);
    sl_natural_add(*nat, digit, &tmp);
    sl_natural_free(nat);
    sl_natural_copy(tmp, nat);
    sl_natural_free(&tmp);

    sl_natural_free(&digit);
  }

  sl_natural_free(&ten);
  return 0;
}

int sl_natural_from_uint64_t(uint64_t n, sl_Natural *nat)
{
  ARR_INIT_RESERVE(nat->digits, 1);
  ARR_APPEND(nat->digits, n);
  return 0; /* TODO: validate array operations. */
}

int sl_natural_copy(sl_Natural src, sl_Natural *dst)
{
  ARR_INIT_RESERVE(dst->digits, ARR_LENGTH(src.digits));
  for (size_t i = 0; i < ARR_LENGTH(src.digits); ++i) {
    uint64_t digit;
    digit = *ARR_GET(src.digits, i);
    ARR_APPEND(dst->digits, digit);
  }
  return 0;
}

void sl_natural_free(sl_Natural *nat)
{
  ARR_FREE(nat->digits);
}

bool sl_natural_equal(sl_Natural a, sl_Natural b)
{
  /* It's okay if the number of digits differ, as long as the leading digits
     are all zero. */
  if (ARR_LENGTH(a.digits) > ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(a.digits) - ARR_LENGTH(b.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(a.digits, i);
      if (digit != 0)
        return FALSE;
    }
    for (size_t i = 0; i < ARR_LENGTH(b.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i + leading);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit != b_digit)
        return FALSE;
    }
  } else if (ARR_LENGTH(a.digits) < ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(b.digits) - ARR_LENGTH(a.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(b.digits, i);
      if (digit != 0)
        return FALSE;
    }
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i + leading);
      if (a_digit != b_digit)
        return FALSE;
    }
  } else { /* ARR_LENGTH(a.digits) == ARR_LENGTH(b.digits) */
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit != b_digit)
        return FALSE;
    }
  }
  return TRUE;
}

bool sl_natural_less_than(sl_Natural a, sl_Natural b)
{
  if (ARR_LENGTH(a.digits) > ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(a.digits) - ARR_LENGTH(b.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(a.digits, i);
      if (digit != 0)
        return FALSE;
    }
    for (size_t i = 0; i < ARR_LENGTH(b.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i + leading);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit < b_digit)
        return TRUE;
      else if (a_digit > b_digit)
        return FALSE;
    }
    return FALSE; /* a == b */
  } else if (ARR_LENGTH(a.digits) < ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(b.digits) - ARR_LENGTH(a.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(b.digits, i);
      if (digit != 0)
          return TRUE;
    }
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i + leading);
      if (a_digit < b_digit)
        return TRUE;
      if (a_digit > b_digit)
        return FALSE;
    }
    return FALSE; /* a == b */
  } else { /* ARR_LENGTH(a.digits) == ARR_LENGTH(b.digits) */
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit < b_digit)
        return TRUE;
      else if (a_digit > b_digit)
        return FALSE;
    }
    return FALSE; /* a == b */
  }
}

bool sl_natural_less_than_equal(sl_Natural a, sl_Natural b)
{
  if (ARR_LENGTH(a.digits) > ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(a.digits) - ARR_LENGTH(b.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(a.digits, i);
      if (digit != 0)
        return FALSE;
    }
    for (size_t i = 0; i < ARR_LENGTH(b.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i + leading);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit < b_digit)
        return TRUE;
      else if (a_digit > b_digit)
        return FALSE;
    }
    return TRUE; /* a == b */
  } else if (ARR_LENGTH(a.digits) < ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(b.digits) - ARR_LENGTH(a.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(b.digits, i);
      if (digit != 0)
          return TRUE;
    }
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i + leading);
      if (a_digit < b_digit)
        return TRUE;
      if (a_digit > b_digit)
        return FALSE;
    }
    return TRUE; /* a == b */
  } else { /* ARR_LENGTH(a.digits) == ARR_LENGTH(b.digits) */
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit < b_digit)
        return TRUE;
      else if (a_digit > b_digit)
        return FALSE;
    }
    return TRUE; /* a == b */
  }
}

bool sl_natural_greater_than(sl_Natural a, sl_Natural b)
{
  return sl_natural_less_than(b, a);
}

bool sl_natural_greater_than_equal(sl_Natural a, sl_Natural b)
{
  return sl_natural_less_than_equal(b, a);
}

int sl_natural_add(sl_Natural a, sl_Natural b, sl_Natural *result)
{
  if (ARR_LENGTH(a.digits) > ARR_LENGTH(b.digits)) {
    size_t leading;
    uint64_t carry;
    sl_Natural sum;
    int err;
    err = sl_natural_from_uint64_t(0, &sum);
    PROPAGATE_ERROR(err);
    leading = ARR_LENGTH(a.digits) - ARR_LENGTH(b.digits);
    for (size_t i = 0; i < ARR_LENGTH(b.digits); ++i) {
      uint64_t a_digit, b_digit, digit_sum, carry;
      a_digit = *ARR_GET(a.digits, ARR_LENGTH(a.digits) - (i + 1));
      b_digit = *ARR_GET(b.digits, ARR_LENGTH(b.digits) - (i + 1));
      digit_sum = a_digit + b_digit;
      if (digit_sum < a_digit)
        carry = 1;
    }
  }
#if 0
  if (ARR_LENGTH(a.digits) > ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(a.digits) - ARR_LENGTH(b.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(a.digits, i);
      if (digit != 0)
        return FALSE;
    }
    for (size_t i = 0; i < ARR_LENGTH(b.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i + leading);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit < b_digit)
        return TRUE;
      else if (a_digit > b_digit)
        return FALSE;
    }
    return TRUE; /* a == b */
  } else if (ARR_LENGTH(a.digits) < ARR_LENGTH(b.digits)) {
    size_t leading;
    leading = ARR_LENGTH(b.digits) - ARR_LENGTH(a.digits);
    for (size_t i = 0; i < leading; ++i) {
      uint64_t digit;
      digit = *ARR_GET(b.digits, i);
      if (digit != 0)
          return TRUE;
    }
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i + leading);
      if (a_digit < b_digit)
        return TRUE;
      if (a_digit > b_digit)
        return FALSE;
    }
    return TRUE; /* a == b */
  } else { /* ARR_LENGTH(a.digits) == ARR_LENGTH(b.digits) */
    for (size_t i = 0; i < ARR_LENGTH(a.digits); ++i) {
      uint64_t a_digit, b_digit;
      a_digit = *ARR_GET(a.digits, i);
      b_digit = *ARR_GET(b.digits, i);
      if (a_digit < b_digit)
        return TRUE;
      else if (a_digit > b_digit)
        return FALSE;
    }
    return TRUE; /* a == b */
  }
#endif
}

int sl_natural_multiply(sl_Natural a, sl_Natural b, sl_Natural *result)
{

}

int sl_natural_divide(sl_Natural a, sl_Natural b, sl_Natural *result)
{

}

int sl_natural_modulo(sl_Natural a, sl_Natural b, sl_Natural *result)
{

}

struct sl_Integer {
  bool is_positive;
  sl_Natural absolute_value;
};

int sl_integer_from_string(const char *str, sl_Integer *intg)
{
  if (str[0] == '-') {
    intg->is_positive = FALSE;
    return sl_natural_from_string(&str[1], &intg->absolute_value);
  } else {
    intg->is_positive = TRUE;
    return sl_natural_from_string(str, &intg->absolute_value);
  }
}

int sl_integer_from_int64_t(int64_t n, sl_Integer *intg)
{
  uint64_t absolute_value_64;
  if (n < 0) {
    intg->is_positive = FALSE;
    absolute_value_64 = (uint64_t)(-n);
  } else {
    intg->is_positive = TRUE;
    absolute_value_64 = (uint64_t)(n);
  }
  return sl_natural_from_uint64_t(absolute_value_64, &intg->absolute_value);
}

int sl_integer_from_natural(sl_Natural nat, sl_Integer *intg)
{
  intg->is_positive = TRUE;
  return sl_natural_copy(nat, &intg->absolute_value);
}

int sl_integer_copy(sl_Integer src, sl_Integer *dst)
{
  dst->is_positive = src.is_positive;
  return sl_natural_copy(dst->absolute_value, &src.absolute_value);
}

void sl_integer_free(sl_Integer *intg)
{
  sl_natural_free(&intg->absolute_value);
}

bool sl_integer_equal(sl_Integer a, sl_Integer b)
{
  return (a.is_positive == b.is_positive)
      && sl_natural_equal(a.absolute_value, b.absolute_value);
}

bool sl_integer_less_than(sl_Integer a, sl_Integer b)
{
  if (a.is_positive && b.is_positive)
    return sl_natural_less_than(a.absolute_value, b.absolute_value);
  else if (a.is_positive && !b.is_positive)
    return FALSE;
  else if (!a.is_positive && b.is_positive)
    return TRUE;
  else /* !a.is_positive && !b.is_positive */
    return sl_natural_less_than(b.absolute_value, a.absolute_value);
}

bool sl_integer_less_than_equal(sl_Integer a, sl_Integer b)
{
  return sl_integer_less_than(a, b) || sl_integer_equal(a, b);
}

bool sl_integer_greater_than(sl_Integer a, sl_Integer b)
{
  return sl_integer_less_than(b, a);
}

bool sl_integer_greater_than_equal(sl_Integer a, sl_Integer b)
{
  return sl_integer_greater_than(a, b) || sl_integer_equal(a, b);
}

int sl_integer_add(sl_Integer a, sl_Integer b, sl_Integer *result)
{
  if (a.is_positive == b.is_positive) {
    result->is_positive = a.is_positive;
    return sl_natural_add(a.absolute_value, b.absolute_value,
        &result->absolute_value);
  } else {

  }
}

int sl_integer_negate(sl_Integer n, sl_Integer *result)
{
  result->is_positive = !result->is_positive;
  return sl_natural_copy(n.absolute_value, &result->absolute_value);
}

int sl_integer_subtract(sl_Integer a, sl_Integer b, sl_Integer *result)
{

}

int sl_integer_multiply(sl_Integer a, sl_Integer b, sl_Integer *result)
{
  int err;
  err = sl_natural_multiply(a.absolute_value, b.absolute_value,
      &result->absolute_value);
  if (a.is_positive == b.is_positive)
    result->is_positive = TRUE;
  else
    result->is_positive = FALSE;
  return err;
}

int sl_integer_divide(sl_Integer a, sl_Integer b, sl_Integer *result)
{
  int err;
  err = sl_natural_divide(a.absolute_value, b.absolute_value,
      &result->absolute_value);
  if (a.is_positive == b.is_positive)
    result->is_positive = TRUE;
  else
    result->is_positive = FALSE;
  return err;
}

int sl_integer_modulo(sl_Integer a, sl_Integer b, sl_Integer *result)
{

}
