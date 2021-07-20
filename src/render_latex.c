#include "render.h"

#define LATEX_BEGIN \
  "\\documentclass[10pt,letterpaper]{article}\n" \
  "\\usepackage{amsmath,amsfonts}\n" \
  "\\usepackage{hyperref}\n" \
  "\\hypersetup{linktoc=all}\n" \
  "\\setlength{\\oddsidemargin}{0in}\n" \
  "\\setlength{\\evensidemargin}{0in}\n" \
  "\\setlength{\\textwidth}{6.5in}\n" \
  "\\setlength{\\topmargin}{-0.4in}\n" \
  "\\setlength{\\textheight}{8.5in}\n" \
  "\\setlength{\\parskip}{0.4em}\n" \
  "\\parindent0em\n" \
  "\\allowdisplaybreaks\n" \
  "\n" \
  "\\begin{document}\n" \
  "\\begin{center}\n" \
  "{\\bf Logic Database}\\medskip\n" \
  "\n" \
  "\\end{center}\n" \
  "\\tableofcontents" \
  "\\pagebreak"

#define LATEX_END \
  "\\end{document}\n"

int
render_theorem(FILE *out)
{
  fputs("\\subsection{theorem}", out);
}

int
render_latex(const LogicState *state, const char *output_filename)
{
  FILE *f = fopen(output_filename, "w");
  fputs(LATEX_BEGIN, f);

  render_theorem(f); /* TODO: tmp. */

  fputs(LATEX_END, f);
  fclose(f);
  return 0;
}
