/*

TODO:
- Verify that judgements are declared before being used.

LANGUAGE DESCRIPTION:

- BUILTINS
-- `is_not_subexpression([A], [B])`

   This requirement is true when `[B]` does not contain any instances of `[A]`
   as a subexpression.

-- `is_substitution([A], [B], [TARGET_EXPR], [SOURCE_EXPR])`

   This requirement is true when `[TARGET_EXPR]` can be formed
   from `[SOURCE_EXPR]` by replacing some occurrences of `[B]` with `[A]`.

-- `is_full_substitution([A], [B], [TARGET_EXPR], [SOURCE_EXPR])`

   This requirement is true when `[TARGET_EXPR]` is formed from `[SOURCE_EXPR]`
   by replacing all occurrences of `[B]` with `[A]`.

*/
#ifndef SOL_H
#define SOL_H

#include <lex.h>
#include <parse.h>

extern int verbose;

int
sol_verify(const char *input_path, FILE *out);

#endif
