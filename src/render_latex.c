#include "render.h"
#include <string.h>
#include <ctype.h>

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

/* In a string, any occurrence of `dst` not next to letters or backslashes
  will be replaced by `src`. */
struct SubstitutionMap
{
  const char *dst;
  const char *src;
};

struct SubstitutionMap greek_letters[] = {
  { "alpha", "\\alpha" },
  { "Alpha", "\\Alpha" },
  { "beta", "\\beta" },
  { "Beta", "\\Beta" },
  { "gamma", "\\gamma" },
  { "Gamma", "\\Gamma" },
  { "delta", "\\delta" },
  { "Delta", "\\Delta" },
  { "epsilon", "\\epsilon" },
  { "Epsilon", "\\Epsilon" },
  { "zeta", "\\zeta" },
  { "Zeta", "\\Zeta" },
  { "eta", "\\eta" },
  { "Eta", "\\Eta" },
  { "theta", "\\theta" },
  { "Theta", "\\Theta" },
  { "iota", "\\iota" },
  { "Iota", "\\Iota" },
  { "kappa", "\\kappa" },
  { "Kappa", "\\Kappa" },
  { "lambda", "\\lambda" },
  { "Lambda", "\\Lambda" },
  { "mu", "\\mu" },
  { "Mu", "\\Mu" },
  { "nu", "\\nu" },
  { "Nu", "\\Nu" },
  { "xi", "\\xi" },
  { "Xi", "\\Xi" },
  { "omicron", "\\omicron" },
  { "Omicron", "\\Omicron" },
  { "pi", "\\pi" },
  { "Pi", "\\Pi" },
  { "rho", "\\rho" },
  { "Rho", "\\Rho" },
  { "sigma", "\\sigma" },
  { "Sigma", "\\Sigma" },
  { "tau", "\\tau" },
  { "Tau", "\\Tau" },
  { "upsilon", "\\upsilon" },
  { "Upsilon", "\\Upsilon" },
  { "phi", "\\phi" },
  { "Phi", "\\Phi" },
  { "chi", "\\chi" },
  { "Chi", "\\Chi" },
  { "psi", "\\psi" },
  { "Psi", "\\Psi" },
  { "omega", "\\omega" },
  { "Omega", "\\Omega" }
};

static char *
do_substitution(const char *src, struct SubstitutionMap map)
{
  /* First calculate the the length. */
  size_t len = 1;
  const char *c = src;
  while (*c != '\0')
  {
    if (c == src && strncmp(c, map.dst, strlen(map.dst)) == 0
      && !isalpha(c[strlen(map.dst)]))
    {
      len += strlen(map.src);
      c += strlen(map.dst);
    }
    else if (c != src && strncmp(c, map.dst, strlen(map.dst)) == 0
      && !isalpha(c[-1]) && *(c - 1) != '\\' && !isalpha(c[strlen(map.dst)]))
    {
      len += strlen(map.src);
      c += strlen(map.dst);
    }
    else
    {
      len += 1;
      ++c;
    }
  }

  char *dst = malloc(len);
  c = src;
  char *write_to = dst;
  while (*c != '\0')
  {
    if (c == src && strncmp(c, map.dst, strlen(map.dst)) == 0
      && !isalpha(c[strlen(map.dst)]))
    {
      strcpy(write_to, map.src);
      c += strlen(map.dst);
      write_to += strlen(map.src);
    }
    else if (c != src && strncmp(c, map.dst, strlen(map.dst)) == 0
      && !isalpha(c[-1]) && *(c - 1) != '\\' && !isalpha(c[strlen(map.dst)]))
    {
      strcpy(write_to, map.src);
      c += strlen(map.dst);
      write_to += strlen(map.src);
    }
    else
    {
      *write_to = *c;
      ++c;
      ++write_to;
    }
  }
  *write_to = '\0';
  return dst;
}

char *
latex_render_string(const char *src)
{
  char *dst = malloc(strlen(src) + 1);
  char *dst_ptr = dst;
  bool in_escape = FALSE;
  for (const char *c = src; *c != '\0'; ++c)
  {
    if (in_escape)
    {
      *dst_ptr = *c;
      ++dst_ptr;
      in_escape = FALSE;
    }
    else
    {
      if (*c == '\\')
      {
        in_escape = TRUE;
      }
      else
      {
        *dst_ptr = *c;
        ++dst_ptr;
      }
    }
  }
  *dst_ptr = '\0';

  for (size_t i = 0; i < sizeof(greek_letters) / sizeof(struct SubstitutionMap);
    ++i)
  {
    char *result = do_substitution(dst, greek_letters[i]);
    free(dst);
    dst = result;
  }

  return dst;
}

char *
latex_render_constant(const struct Constant *c)
{
  char *result;
  Array segments;
  ARRAY_INIT(segments, char *);
  size_t len = 1;
  for (size_t i = 0; i < ARRAY_LENGTH(c->latex.segments); ++i)
  {
    const struct LatexFormatSegment *seg =
      ARRAY_GET(c->latex.segments, struct LatexFormatSegment, i);
    char *str = latex_render_string(seg->string);
    ARRAY_APPEND(segments, char *, str);
    len += strlen(str);
  }
  result = malloc(len);
  char *result_ptr = result;
  for (size_t i = 0; i < ARRAY_LENGTH(segments); ++i)
  {
    char *seg = *ARRAY_GET(segments, char *, i);
    strcpy(result_ptr, seg);
    result_ptr += strlen(seg);
  }
  *result_ptr = '\0';
  return result;
}

char *
latex_render_expression(const struct Expression *e)
{
  char *result;
  Array segments;
  ARRAY_INIT(segments, char *);
  size_t len = 1;
  for (size_t i = 0; i < ARRAY_LENGTH(e->latex.segments); ++i)
  {
    const struct LatexFormatSegment *seg =
      ARRAY_GET(e->latex.segments, struct LatexFormatSegment, i);
    char *str = latex_render_string(seg->string);
    ARRAY_APPEND(segments, char *, str);
    len += strlen(str);
  }
  result = malloc(len);
  char *result_ptr = result;
  for (size_t i = 0; i < ARRAY_LENGTH(segments); ++i)
  {
    char *seg = *ARRAY_GET(segments, char *, i);
    strcpy(result_ptr, seg);
    result_ptr += strlen(seg);
  }
  *result_ptr = '\0';
  return result;
}

char *
latex_render_value(const Value *v)
{
  switch (v->value_type)
  {
    case ValueTypeConstant:
      if (v->constant->has_latex)
        return latex_render_constant(v->constant);
      else
        return strdup(get_symbol_path_last_segment(v->constant->path));
      break;
    case ValueTypeVariable:
      return latex_render_string(v->variable_name);
      break;
    case ValueTypeComposition:
      if (v->expression->has_latex)
      {
        char *result;
        Array segments;
        ARRAY_INIT(segments, char *);
        size_t len = 1;
        for (size_t i = 0; i < ARRAY_LENGTH(v->expression->latex.segments); ++i)
        {
          const struct LatexFormatSegment *seg =
            ARRAY_GET(v->expression->latex.segments,
            struct LatexFormatSegment, i);
          char *str;
          if (seg->is_variable)
          {
            /* Find the corresponding argument. */
            size_t arg_index;
            for (size_t j = 0; j < ARRAY_LENGTH(v->expression->parameters); ++j)
            {
              const struct Parameter *param =
                ARRAY_GET(v->expression->parameters, struct Parameter, j);
              if (strcmp(param->name, seg->string) == 0)
              {
                arg_index = j;
                break;
              }
            }
            Value *arg = *ARRAY_GET(v->arguments, Value *, arg_index);
            str = latex_render_value(arg);
          }
          else
          {
            str = latex_render_string(seg->string);
          }
          ARRAY_APPEND(segments, char *, str);
          len += strlen(str);
        }
        result = malloc(len);
        char *result_ptr = result;
        for (size_t i = 0; i < ARRAY_LENGTH(segments); ++i)
        {
          char *seg = *ARRAY_GET(segments, char *, i);
          strcpy(result_ptr, seg);
          result_ptr += strlen(seg);
        }
        *result_ptr = '\0';
        return result;
      }
      else
      {
        return strdup("");
      }
      break;
  }
}
