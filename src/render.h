#ifndef RENDER_H
#define RENDER_H

#include "logic.h"

int
render_html(const LogicState *state, const char *output_dir);

int
render_latex(const LogicState *state, const char *output_filename);

#endif
