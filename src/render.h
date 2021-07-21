#ifndef RENDER_H
#define RENDER_H

#include "logic.h"
#include "core.h"

/* HTML */
int
render_html(const LogicState *state, const char *output_dir);

/* LaTeX */
char *
latex_render_string(const char *src);

int
render_latex(const LogicState *state, const char *output_filename);

char *
latex_render_constant(const struct Constant *c);

char *
latex_render_expression(const struct Expression *e);

char *
latex_render_value(const Value *v);

#endif
