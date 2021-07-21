#include "render.h"
#include "common.h"
#include "core.h"
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>

#define HTML_HEAD_FORMAT \
  "<!doctype html>\n" \
  "<html>\n" \
  "<head>\n" \
  "<meta charset=\"utf-8\">\n" \
  "<script src=\"https://polyfill.io/v3/polyfill.js?features=es6\"></script>\n" \
  "<script id=\"MathJax-script\" async src=\"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js\"></script>\n" \
  "<title>%s</title>\n" \
  "</head>\n"
#define HTML_END "</html>\n"

char *
html_head(const char *title)
{
  char *dst;
  asprintf(&dst, HTML_HEAD_FORMAT, title);
  return dst;
}

char *
html_render_value(const Value *v)
{
  char *str;
  switch (v->value_type)
  {
    case ValueTypeConstant:
      asprintf(&str, "<a href=\"#sym-%zu\">%s</a>",
        v->constant->id,
        get_symbol_path_last_segment(v->constant->path));
      break;
    case ValueTypeVariable:
      asprintf(&str, "$%s", v->variable_name);
      break;
    case ValueTypeComposition:
      if (ARRAY_LENGTH(v->arguments) == 0)
      {
        asprintf(&str, "<a href=\"#sym-%zu\">%s</a>()",
          v->expression->id,
          get_symbol_path_last_segment(v->expression->path));
      }
      else
      {
        size_t args_str_len = 1;
        char **args = malloc(sizeof(char *) * ARRAY_LENGTH(v->arguments));
        for (size_t i = 0; i < ARRAY_LENGTH(v->arguments); ++i)
        {
          const Value *arg = *ARRAY_GET(v->arguments, struct Value *, i);
          args[i] = html_render_value(arg);
          args_str_len += strlen(args[i]);
        }
        args_str_len += (ARRAY_LENGTH(v->arguments) - 1) * 2;

        char *args_str = malloc(args_str_len);
        char *c = args_str;
        bool first_arg = TRUE;
        for (size_t i = 0; i < ARRAY_LENGTH(v->arguments); ++i)
        {
          if (!first_arg)
          {
            strcpy(c, ", ");
            c += 2;
          }
          if (first_arg)
            first_arg = FALSE;
          strcpy(c, args[i]);
          c += strlen(args[i]);
          free(args[i]);
        }
        free(args);
        *c = '\0';

        asprintf(&str, "<a href=\"#sym-%zu\">%s</a>(%s)",
          v->expression->id,
          get_symbol_path_last_segment(v->expression->path),
          args_str);
        free(args_str);
      }
      break;
  }
  return str;
}

int
html_render_type(const struct Type *type, FILE *f)
{
  fputs("<div class=\"symbol\">\n", f);
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%zu\">\n", type->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    if (type->atomic)
      asprintf(&id_label, "<h3><code>%zu:</code> Atomic Type</h3>\n", type->id);
    else
      asprintf(&id_label, "<h3><code>%zu:</code> Type</h3>\n", type->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = string_from_symbol_path(type->path);
    char *type_label;
    asprintf(&type_label, "<h4>Path: <code>%s</code></h4>\n", path);
    fputs(type_label, f);
    free(path);
    free(type_label);
  }
  fputs("</div>\n", f);
  return 0;
}

int
html_render_constant(const struct Constant *constant, FILE *f)
{
  fputs("<div class=\"symbol\">\n", f);
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%zu\">\n", constant->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    asprintf(&id_label, "<h3><code>%zu:</code> Constant</h3>\n", constant->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = string_from_symbol_path(constant->path);
    char *type_label;
    asprintf(&type_label, "<h4>Path: <code>%s</code></h4>\n", path);
    fputs(type_label, f);
    free(path);
    free(type_label);
  }
  {
    char *const_type = string_from_symbol_path(constant->type->path);
    char *type_label;
    asprintf(&type_label,
      "<h4>Type: <code><a href=\"#sym-%zu\">%s</a></code></h4>\n",
      constant->type->id, const_type);
    fputs(type_label, f);
    free(const_type);
    free(type_label);
  }
  if (constant->latex != NULL)
  {
    char *latex = latex_render_constant(constant->latex);
    char *latex_label;
    asprintf(&latex_label, "<h4>LaTeX: \\(%s\\)</h4>\n", latex);
    fputs(latex_label, f);
    free(latex);
    free(latex_label);
  }
  fputs("</div>\n", f);
  return 0;
}

int
html_render_expression(const struct Expression *expression, FILE *f)
{
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%zu\">\n",
      expression->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    asprintf(&id_label, "<h3><code>%zu:</code> Expression</h3>\n",
      expression->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = string_from_symbol_path(expression->path);
    char *path_label;
    asprintf(&path_label, "<h4>Path: <code>%s</code></h4>\n", path);
    fputs(path_label, f);
    free(path);
    free(path_label);
  }
  {
    char *expr_type = string_from_symbol_path(expression->type->path);
    char *type_label;
    asprintf(&type_label,
      "<h4>Type: <code><a href=\"#sym-%zu\">%s</a></code></h4>\n",
      expression->type->id, expr_type);
    fputs(type_label, f);
    free(expr_type);
    free(type_label);
  }
  fputs("<h4>Parameters:</h4>\n", f);
  fputs("<ol>\n", f);
  for (size_t i = 0; i < ARRAY_LENGTH(expression->parameters); ++i)
  {
    const struct Parameter *param =
      ARRAY_GET(expression->parameters, struct Parameter, i);
    char *param_type = string_from_symbol_path(param->type->path);
    char *param_label;
    asprintf(&param_label,
      "<li><code>%s</code> : <code><a href=\"#sym-%zu\">%s</a></code></li>\n",
      param->name, param->type->id, param_type);
    fputs(param_label, f);
    free(param_type);
    free(param_label);
  }
  if (expression->latex != NULL)
  {
    char *latex = latex_render_constant(expression->latex);
    char *latex_label;
    asprintf(&latex_label, "<h4>LaTeX: \\(%s\\)</h4>\n", latex);
    fputs(latex_label, f);
    free(latex);
    free(latex_label);
  }
  fputs("</ol>\n", f);
  fputs("</div>\n", f);
  return 0;
}

int
html_render_theorem(const struct Theorem *theorem, FILE *f)
{
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%zu\">\n", theorem->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    if (theorem->is_axiom)
      asprintf(&id_label, "<h3><code>%zu:</code> Axiom</h3>\n", theorem->id);
    else
      asprintf(&id_label, "<h3><code>%zu:</code> Theorem</h3>\n", theorem->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = string_from_symbol_path(theorem->path);
    char *path_label;
    asprintf(&path_label, "<h4>Path: <code>%s</code></h4>\n", path);
    fputs(path_label, f);
    free(path);
    free(path_label);
  }
  fputs("<h4>Parameters:</h4>\n", f);
  fputs("<ol>\n", f);
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->parameters); ++i)
  {
    const struct Parameter *param =
      ARRAY_GET(theorem->parameters, struct Parameter, i);
    char *param_type = string_from_symbol_path(param->type->path);
    char *param_label;
    asprintf(&param_label,
      "<li><code>%s</code> : <code><a href=\"#sym-%zu\">%s</a></code></li>\n",
      param->name, param->type->id, param_type);
    fputs(param_label, f);
    free(param_type);
    free(param_label);
  }
  fputs("</ol>\n", f);
  fputs("<h4>Assumptions:</h4>\n", f);
  fputs("<ul>\n", f);
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->assumptions); ++i)
  {
    const Value *assume = *ARRAY_GET(theorem->assumptions, Value *, i);
    char *assume_str = html_render_value(assume);
    char *assume_label;
    asprintf(&assume_label, "<li><code>%s</code></li>\n", assume_str);
    fputs(assume_label, f);
    free(assume_str);
    free(assume_label);
  }
  fputs("</ul>\n", f);
  fputs("<h4>Inferences:</h4>\n", f);
  fputs("<ul>\n", f);
  for (size_t i = 0; i < ARRAY_LENGTH(theorem->inferences); ++i)
  {
    const Value *infer = *ARRAY_GET(theorem->inferences, Value *, i);
    char *infer_str = html_render_value(infer);
    char *infer_label;
    asprintf(&infer_label, "<li><code>%s</code></li>\n", infer_str);
    fputs(infer_label, f);
    free(infer_str);
    free(infer_label);
  }
  fputs("</ul>\n", f);
  fputs("</div>\n", f);
  return 0;
}

int
html_render_index(const LogicState *state, const char *filepath)
{
  FILE *f = fopen(filepath, "w");
  if (f == NULL)
    return 1;
  {
    char *head = html_head("Index");
    fputs(head, f);
    free(head);
  }
  fputs("<h1>Index of Logic Database</h1>\n", f);

  /* Run through all the namespaces. */
  fputs("<h2>Table of Contents</h2>\n", f);

  /* Print out all the symbols. */
  for (size_t i = 0; i < ARRAY_LENGTH(state->symbol_table); ++i)
  {
    const struct Symbol *sym =
      ARRAY_GET(state->symbol_table, struct Symbol, i);
    if (sym->type == SymbolTypeType)
      html_render_type((struct Type *)sym->object, f);
    else if (sym->type == SymbolTypeConstant)
      html_render_constant((struct Constant *)sym->object, f);
    else if (sym->type == SymbolTypeExpression)
      html_render_expression((struct Expression *)sym->object, f);
    else if (sym->type == SymbolTypeTheorem)
      html_render_theorem((struct Theorem *)sym->object, f);
  }

  fputs(HTML_END, f);
  fclose(f);
  return 0;
}

int
render_html(const LogicState *state, const char *output_dir)
{
  mkdir(output_dir, 0777); /* TODO: handle errors. */

  {
    char index_path[1024];
    snprintf(index_path, 1024, "%s/index.html", output_dir);
    int err = html_render_index(state, index_path);
    PROPAGATE_ERROR(err);
  }
  return 0;
}
