/*

TODO:
-

*/
#ifndef SL_H
#define SL_H

#include <lex.h>
#include <parse.h>

extern int verbose;

int
sl_verify(const char *input_path, FILE *out);

#endif
