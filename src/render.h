#ifndef RENDER_H
#define RENDER_H

#include "logic.h"
#include "core.h"

/* HTML */
int
render_html(const sl_LogicState *state, const char *output_dir);

/* LaTeX */
char *
latex_render_string(const char *src);

int
render_latex(const sl_LogicState *state, const char *output_filename);

char *
latex_render_constant(const sl_LogicState *state, const struct Constant *c);

char *
latex_render_expression(const sl_LogicState *state,
  const struct Expression *e);

char *
latex_render_value(const sl_LogicState *state, const Value *v);

#endif
