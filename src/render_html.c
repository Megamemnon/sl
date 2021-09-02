#include "render.h"
#include "common.h"
#include "core.h"
#include "parse.h"
#include <unistd.h>
#include <string.h>
#include <sys/stat.h>

#define LINE_BUFFER_SIZE 4096

typedef int (* sl_html_generator_t)(FILE *, void *);

struct sl_HTMLTemplateSubstituion {
  const char *target;
  sl_html_generator_t generate;
  void *userdata;
};

static int sl_load_html_template(const char *template_path, FILE *out,
    struct sl_HTMLTemplateSubstituion *substitutions, size_t substitutions_n)
{
  sl_TextInput *input;
  sl_TextInputLineBuffer *buf;
  const char *line;
  /* Load the file, and read through until we find special tags. Then
     replace the content of each special tag using the provided callback. If
     there is no such tag, just leave it in place. */
  input = sl_input_from_file(template_path);
  if (input == NULL)
    return 1;
  buf = sl_input_make_line_buffer(LINE_BUFFER_SIZE);
  if (buf == NULL) {
    sl_input_free(input);
    return 1;
  }

  while (sl_input_get_line(input, buf) == 0) {
    /* Look through the line for special tags. If we find any, find the
       corresponding substitution and insert it. If no such substitution
       exists or another error occurs, just emit a warning and write the
       name of the substitution. */
    bool in_tag;
    char output_buf[LINE_BUFFER_SIZE];
    char *output_cursor;
    line = sl_input_get_line_buffer_contents(buf);
    output_cursor = output_buf;
    for (const char *c = line; *c != '\0'; ++c) {
      if (!in_tag) {
        if (strlen(c) >= 2 && strncmp(c, "<@", 2) == 0) {
          in_tag = TRUE;
          ++c;
          /* TODO: handle errors. */
          fwrite(output_buf, 1, output_cursor - output_buf, out);
          output_cursor = output_buf;
        } else {
          *output_cursor = *c;
          ++output_cursor;
        }
      } else {
        if (strlen(c) >= 2 && strncmp(c, "@>", 2) == 0) {
          bool found_sub = FALSE;
          in_tag = FALSE;
          ++c;
          /* TODO: handle errors. */
          *output_cursor = '\0';
          ++output_cursor;
          for (size_t i = 0; i < substitutions_n; ++i) {
            struct sl_HTMLTemplateSubstituion sub = substitutions[i];
            if (strcmp(sub.target, output_buf) == 0) {
              sub.generate(out, sub.userdata);
              found_sub = TRUE;
            }
          }
          if (!found_sub) {
            printf("found tag \"%s\" without a corresponding generator\n",
                output_buf);
            fwrite(output_buf, 1, output_cursor - output_buf, out);
          }
          output_cursor = output_buf;
        } else if (!isspace(*c)) {
          *output_cursor = *c;
          ++output_cursor;
        }
      }
    }
    /* If we have an unterminated tag, just fill it in and emit a warning. */
    if (in_tag) {
      /* TODO: warning. */
    } else {
      fwrite(output_buf, 1, output_cursor - output_buf, out);
      output_cursor = output_buf;
    }
  }

  sl_input_free(input);
  sl_input_free_line_buffer(buf);
  return 0;
}

struct sl_HTMLFileInfo;

typedef int (* sl_html_write_content_t)(struct sl_HTMLFileInfo *);

struct sl_HTMLFileInfo {
  const char *output_path;
  const char *page_name;
  sl_html_write_content_t content;
  void *userdata;
};

static int substitute_title(FILE *out, void *userdata)
{
  struct sl_HTMLFileInfo *info = (struct sl_HTMLFileInfo *)userdata;
  fputs(info->page_name, out); /* TODO: handle error. */
  return 0;
}

int sl_generate_full_html_file(struct sl_HTMLFileInfo *info)
{
  struct sl_HTMLTemplateSubstituion substitutions[1];
  if (info == NULL)
    return 0;
  {
    /* Title */
    substitutions[0].target = "page_title";
    substitutions[0].generate = &substitute_title;
    substitutions[0].userdata = info;
  }
  {
    FILE *f = fopen(info->output_path, "w");
    sl_load_html_template("res/page.html", f, substitutions, 1);
    fclose(f);
  }
  return 0;
}

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
html_render_value(const sl_LogicState *state, const Value *v)
{
  char *str;
  switch (v->value_type)
  {
    case ValueTypeDummy:
      asprintf(&str, "Dummy %u", v->content.dummy_id);
      break;
    case ValueTypeConstant:
      asprintf(&str, "<a href=\"#sym-%u\">%s</a>",
        /*v->constant->id*/ 0,
        sl_get_symbol_path_last_segment(state,
            v->content.constant.constant_path));
      break;
    case ValueTypeVariable:
      asprintf(&str, "$%s",
          logic_state_get_string(state, v->content.variable_name_id));
      break;
    case ValueTypeComposition:
      if (ARR_LENGTH(v->content.composition.arguments) == 0)
      {
        const sl_SymbolPath *expr_path = sl_logic_get_symbol_path_by_id(state,
            v->content.composition.expression_id);
        asprintf(&str, "<a href=\"#sym-%u\">%s</a>()",
          v->content.composition.expression_id,
          sl_get_symbol_path_last_segment(state, expr_path));
      }
      else
      {
        size_t args_str_len = 1;
        char **args = malloc(sizeof(char *)
            * ARR_LENGTH(v->content.composition.arguments));
        for (size_t i = 0; i < ARR_LENGTH(v->content.composition.arguments);
            ++i) {
          const Value *arg = *ARR_GET(v->content.composition.arguments, i);
          args[i] = html_render_value(state, arg);
          args_str_len += strlen(args[i]);
        }
        args_str_len += (ARR_LENGTH(v->content.composition.arguments) - 1) * 2;

        char *args_str = malloc(args_str_len);
        char *c = args_str;
        bool first_arg = TRUE;
        for (size_t i = 0; i < ARR_LENGTH(v->content.composition.arguments);
            ++i) {
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

        const sl_SymbolPath *expr_path = sl_logic_get_symbol_path_by_id(state,
            v->content.composition.expression_id);
        asprintf(&str, "<a href=\"#sym-%u\">%s</a>(%s)",
            v->content.composition.expression_id,
            sl_get_symbol_path_last_segment(state, expr_path), args_str);
        free(args_str);
      }
      break;
  }
  return str;
}

int
html_render_type(const sl_LogicState *state, const struct Type *type, FILE *f)
{
  fputs("<div class=\"symbol\">\n", f);
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%u\">\n", type->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    if (type->atomic)
      asprintf(&id_label, "<h3><code>%u:</code> Atomic Type</h3>\n", type->id);
    else
      asprintf(&id_label, "<h3><code>%u:</code> Type</h3>\n", type->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = sl_string_from_symbol_path(state, type->path);
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
html_render_constant(const sl_LogicState *state,
  const struct Constant *constant, FILE *f)
{
  fputs("<div class=\"symbol\">\n", f);
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%u\">\n", constant->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    asprintf(&id_label, "<h3><code>%u:</code> Constant</h3>\n", constant->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = sl_string_from_symbol_path(state, constant->path);
    char *type_label;
    asprintf(&type_label, "<h4>Path: <code>%s</code></h4>\n", path);
    fputs(type_label, f);
    free(path);
    free(type_label);
  }
  {
    const sl_SymbolPath *const_path;
    const_path = sl_logic_get_symbol_path_by_id(state, constant->type_id);
    char *const_type = sl_string_from_symbol_path(state, const_path);
    char *type_label;
    asprintf(&type_label,
      "<h4>Type: <code><a href=\"#sym-%u\">%s</a></code></h4>\n",
      constant->type_id, const_type);
    fputs(type_label, f);
    free(const_type);
    free(type_label);
  }
  if (constant->latex_format != NULL)
  {
    char *latex = latex_render_constant(state, constant);
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
html_render_expression(const sl_LogicState *state,
  const struct Expression *expression, FILE *f)
{
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%u\">\n",
      expression->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    asprintf(&id_label, "<h3><code>%u:</code> Expression</h3>\n",
      expression->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = sl_string_from_symbol_path(state, expression->path);
    char *path_label;
    asprintf(&path_label, "<h4>Path: <code>%s</code></h4>\n", path);
    fputs(path_label, f);
    free(path);
    free(path_label);
  }
  {
    const sl_SymbolPath *type_path
        = sl_logic_get_symbol_path_by_id(state, expression->type_id);
    char *expr_type = sl_string_from_symbol_path(state, type_path);
    char *type_label;
    asprintf(&type_label,
      "<h4>Type: <code><a href=\"#sym-%u\">%s</a></code></h4>\n",
      expression->type_id, expr_type);
    fputs(type_label, f);
    free(expr_type);
    free(type_label);
  }
  if (ARR_LENGTH(expression->parameters) > 0)
  {
    fputs("<h4>Parameters:</h4>\n", f);
    fputs("<ol>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(expression->parameters); ++i)
    {
      const struct Parameter *param = ARR_GET(expression->parameters, i);
      const sl_SymbolPath *type_path = sl_logic_get_symbol_path_by_id(state,
          param->type_id);
      char *param_type = sl_string_from_symbol_path(state, type_path);
      char *param_str = latex_render_string(logic_state_get_string(state,
          param->name_id));
      char *param_label;
      asprintf(&param_label,
        "<li><code>%s</code> : <code><a href=\"#sym-%u\">%s</a></code><br />\\(%s\\)</li>\n",
        logic_state_get_string(state, param->name_id),
        param->type_id, param_type, param_str);
      fputs(param_label, f);
      free(param_type);
      free(param_str);
      free(param_label);
    }
    fputs("</ol>\n", f);
  }
  if (expression->replace_with != NULL) {
    char *abbreviates_label, *abbreviates_str, *abbreviates_latex;
    abbreviates_str = html_render_value(state, expression->replace_with);
    abbreviates_latex = latex_render_value(state, expression->replace_with);
    asprintf(&abbreviates_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
        abbreviates_str, abbreviates_latex);
    fputs("<h4>Abbreviates:</h4>\n", f);
    fputs(abbreviates_label, f);
    free(abbreviates_label);
    free(abbreviates_str);
    free(abbreviates_latex);
  }
  if (expression->has_latex)
  {
    char *latex = latex_render_expression(state, expression);
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
html_render_theorem(const sl_LogicState *state, const struct Theorem *theorem,
  FILE *f)
{
  {
    char *div_begin;
    asprintf(&div_begin, "<div class=\"symbol\" id=\"sym-%u\">\n", theorem->id);
    fputs(div_begin, f);
    free(div_begin);
  }
  {
    char *id_label;
    if (theorem->is_axiom)
      asprintf(&id_label, "<h3><code>%u:</code> Axiom</h3>\n", theorem->id);
    else
      asprintf(&id_label, "<h3><code>%u:</code> Theorem</h3>\n", theorem->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = sl_string_from_symbol_path(state, theorem->path);
    char *path_label;
    asprintf(&path_label, "<h4>Path: <code><a href=\"./symbols/theorem-%u.html\">%s</a></code></h4>\n",
      theorem->id, path);
    fputs(path_label, f);
    free(path);
    free(path_label);
  }
  if (ARR_LENGTH(theorem->requirements) > 0) {
    fputs("<h4>Requirements:</h4>\n", f);
    fputs("<ul>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->requirements); ++i) {
      const struct Requirement *req = ARR_GET(theorem->requirements, i);
      switch (req->type) {
        case RequirementTypeDistinct:
          fputs("<li><h5>Distinct:</h5><ul>\n", f);
          for (size_t j = 0; j < ARR_LENGTH(req->arguments); ++j) {
            const Value *arg = *ARR_GET(req->arguments, j);
            char *arg_str = html_render_value(state, arg);
            char *arg_latex = latex_render_value(state, arg);
            char *arg_label;
            asprintf(&arg_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
              arg_str, arg_latex);
            fputs(arg_label, f);
            free(arg_str);
            free(arg_latex);
            free(arg_label);
          }
          fputs("</ul></li>\n", f);
          break;
        case RequirementTypeFreeFor:
          break;
        case RequirementTypeNotFree:
          break;
        case RequirementTypeCoverFree:
          break;
        case RequirementTypeSubstitution:
          break;
        case RequirementTypeFullSubstitution:
          break;
        case RequirementTypeUnused:
          break;
      }
    }
    fputs("</ul>\n", f);
  }
  if (ARR_LENGTH(theorem->parameters))
  {
    fputs("<h4>Parameters:</h4>\n", f);
    fputs("<ol>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->parameters); ++i)
    {
      const struct Parameter *param = ARR_GET(theorem->parameters, i);
      const sl_SymbolPath *type_path = sl_logic_get_symbol_path_by_id(state,
          param->type_id);
      char *param_type = sl_string_from_symbol_path(state, type_path);
      char *param_str = latex_render_string(logic_state_get_string(state,
          param->name_id));
      char *param_label;
      asprintf(&param_label,
        "<li><code>%s</code> : <code><a href=\"#sym-%u\">%s</a></code><br />\\(%s\\)</li>\n",
          logic_state_get_string(state, param->name_id),
          param->type_id, param_type, param_str);
      fputs(param_label, f);
      free(param_type);
      free(param_str);
      free(param_label);
    }
    fputs("</ol>\n", f);
  }
  if (ARR_LENGTH(theorem->assumptions))
  {
    fputs("<h4>Assumptions:</h4>\n", f);
    fputs("<ul>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->assumptions); ++i)
    {
      const Value *assume = *ARR_GET(theorem->assumptions, i);
      char *assume_str = html_render_value(state, assume);
      char *assume_latex = latex_render_value(state, assume);
      char *assume_label;
      asprintf(&assume_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
        assume_str, assume_latex);
      fputs(assume_label, f);
      free(assume_str);
      free(assume_latex);
      free(assume_label);

    }
    fputs("</ul>\n", f);
  }
  if (ARR_LENGTH(theorem->inferences))
  {
    fputs("<h4>Inferences:</h4>\n", f);
    fputs("<ul>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->inferences); ++i)
    {
      const Value *infer = *ARR_GET(theorem->inferences, i);
      char *infer_str = html_render_value(state, infer);
      char *infer_latex = latex_render_value(state, infer);
      char *infer_label;
      asprintf(&infer_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
        infer_str, infer_latex);
      fputs(infer_label, f);
      free(infer_str);
      free(infer_latex);
      free(infer_label);
    }
    fputs("</ul>\n", f);
  }
  fputs("</div>\n", f);
  return 0;
}

int
html_render_all_page(const sl_LogicState *state, const char *filepath)
{
  FILE *f = fopen(filepath, "w");
  if (f == NULL)
    return 1;
  {
    char *head = html_head("All Symbols");
    fputs(head, f);
    free(head);
  }
  fputs("<h1>All Symbols</h1>\n", f);

  /* Print out all the symbols. */
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    const sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    if (sym->type == sl_LogicSymbolType_Type)
      html_render_type(state, (struct Type *)sym->object, f);
    else if (sym->type == sl_LogicSymbolType_Constant)
      html_render_constant(state, (struct Constant *)sym->object, f);
    else if (sym->type == sl_LogicSymbolType_Expression)
      html_render_expression(state, (struct Expression *)sym->object, f);
    else if (sym->type == sl_LogicSymbolType_Theorem)
      html_render_theorem(state, (struct Theorem *)sym->object, f);
  }

  fputs(HTML_END, f);
  fclose(f);
  return 0;
}

static void render_symbol_count(const sl_LogicState *state,
  sl_LogicSymbolType type, const char *type_name_plural, FILE *out)
{
  size_t symbols_n = sl_logic_count_symbols_of_type(state, type);
  char *symbols_string;
  asprintf(&symbols_string, "<li><p>%zu %s.</p></li>\n", symbols_n,
    type_name_plural);
  fputs(symbols_string, out);
  free(symbols_string);
}

static int html_render_index_page(const sl_LogicState *state,
  const char *filepath)
{
  struct sl_HTMLFileInfo file_info;
  file_info.output_path = filepath;
  file_info.page_name = "Index";
  file_info.content = NULL;
  file_info.userdata = NULL;
  sl_generate_full_html_file(&file_info);
#if 0
  FILE *f = fopen(filepath, "w");
  if (f == NULL)
    return 1;
  {
    char *head = html_head("Index");
    fputs(head, f);
    free(head);
  }
  fputs("<h1>Index of Logic Database</h1>\n", f);

  {
    fputs("<div id=\"statistics\">\n", f);
    fputs("<p>This database contains...</p>\n<ul>", f);
    {
      char *symbols_string;
      size_t symbols_n = sl_logic_count_symbols(state);
      asprintf(&symbols_string, "<li><p>%zu symbol(s).</p></li>\n", symbols_n);
      fputs(symbols_string, f);
      free(symbols_string);
    }
    render_symbol_count(state, sl_LogicSymbolType_Namespace,
        "namespace(s)", f);
    render_symbol_count(state, sl_LogicSymbolType_Type, "type(s)", f);
    render_symbol_count(state, sl_LogicSymbolType_Constant,
        "constant(s)", f);
    render_symbol_count(state, sl_LogicSymbolType_Constspace,
        "constspace(s)", f);
    render_symbol_count(state, sl_LogicSymbolType_Expression,
        "expression(s)", f);
    render_symbol_count(state, sl_LogicSymbolType_Theorem, "theorem(s)", f);
    fputs("</ul>\n</div>\n", f);
  }

  fputs(HTML_END, f);
  fclose(f);
#endif
  return 0;
}

int
html_render_theorem_page(const sl_LogicState *state,
  const struct Theorem *theorem, const char *filepath)
{
  FILE *f = fopen(filepath, "w");
  if (f == NULL)
    return 1;
  {
    char *head = html_head(sl_get_symbol_path_last_segment(state,
      theorem->path));
    fputs(head, f);
    free(head);
  }

  {
    char *id_label;
    if (theorem->is_axiom)
      asprintf(&id_label, "<h1><code>%u:</code> Axiom</h1>\n", theorem->id);
    else
      asprintf(&id_label, "<h1><code>%u:</code> Theorem</h1>\n", theorem->id);
    fputs(id_label, f);
    free(id_label);
  }
  {
    char *path = sl_string_from_symbol_path(state, theorem->path);
    char *path_label;
    asprintf(&path_label, "<h2>Path: <code>%s</code></h2>\n", path);
    fputs(path_label, f);
    free(path);
    free(path_label);
  }
  if (ARR_LENGTH(theorem->parameters))
  {
    fputs("<h2>Parameters:</h2>\n", f);
    fputs("<ol>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->parameters); ++i)
    {
      const struct Parameter *param = ARR_GET(theorem->parameters, i);
      const sl_SymbolPath *type_path = sl_logic_get_symbol_path_by_id(state,
          param->type_id);
      char *param_type = sl_string_from_symbol_path(state, type_path);
      char *param_str = latex_render_string(logic_state_get_string(state,
          param->name_id));
      char *param_label;
      asprintf(&param_label,
          "<li><code>%s</code> : <code><a href=\"#sym-%u\">%s</a></code><br />\\(%s\\)</li>\n",
          logic_state_get_string(state, param->name_id),
          param->type_id, param_type, param_str);
      fputs(param_label, f);
      free(param_type);
      free(param_str);
      free(param_label);
    }
    fputs("</ol>\n", f);
  }
  if (ARR_LENGTH(theorem->assumptions))
  {
    fputs("<h2>Assumptions:</h2>\n", f);
    fputs("<ul>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->assumptions); ++i)
    {
      const Value *assume = *ARR_GET(theorem->assumptions, i);
      char *assume_str = html_render_value(state, assume);
      char *assume_latex = latex_render_value(state, assume);
      char *assume_label;
      asprintf(&assume_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
        assume_str, assume_latex);
      fputs(assume_label, f);
      free(assume_str);
      free(assume_latex);
      free(assume_label);

    }
    fputs("</ul>\n", f);
  }
  if (ARR_LENGTH(theorem->inferences))
  {
    fputs("<h2>Inferences:</h2>\n", f);
    fputs("<ul>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->inferences); ++i)
    {
      const Value *infer = *ARR_GET(theorem->inferences, i);
      char *infer_str = html_render_value(state, infer);
      char *infer_latex = latex_render_value(state, infer);
      char *infer_label;
      asprintf(&infer_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
        infer_str, infer_latex);
      fputs(infer_label, f);
      free(infer_str);
      free(infer_latex);
      free(infer_label);
    }
    fputs("</ul>\n", f);
  }
  /*if (!theorem->is_axiom)
  {
    fputs("<div>\n", f);
    fputs("<h4>Steps:</h4>\n", f);
    fputs("<ol>\n", f);
    for (size_t i = 0; i < ARR_LENGTH(theorem->steps); ++i)
    {
      struct TheoremReference *ref = ARR_GET(theorem->steps, i);
      fputs("<li><div>\n", f);
      {
        char *path = string_from_symbol_path(ref->theorem->path);
        char *path_label;
        asprintf(&path_label, "<h4>Path: <code><a href=\"../symbols/theorem-%u.html\">%s</a></code></h4>\n",
          ref->theorem->id, path);
        fputs(path_label, f);
        free(path);
        free(path_label);
      }
      fputs("<h4>Arguments: </h4>\n", f);
      fputs("<ol>\n", f);
      for (size_t j = 0; j < ARR_LENGTH(ref->arguments); ++j)
      {
        const Value *arg = *ARR_GET(ref->arguments, j);
        char *arg_str = html_render_value(arg);
        char *arg_latex = latex_render_value(arg);
        char *arg_label;
        asprintf(&arg_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
          arg_str, arg_latex);
        fputs(arg_label, f);
        free(arg_str);
        free(arg_latex);
        free(arg_label);
      }
      fputs("</ol>\n", f);
      fputs("<h4>Inferred: </h4>\n", f);
      fputs("<ul>\n", f);
      {
        ValueArray proven_arr;
        ARR_INIT(proven_arr);
        ArgumentArray args;
        ARR_INIT(args);
        for (size_t j = 0; j < ARR_LENGTH(ref->arguments); ++j)
        {
          struct Parameter *param = ARR_GET(ref->theorem->parameters, j);

          struct Argument arg;
          arg.name = strdup(param->name);
          arg.value = copy_value(*ARR_GET(ref->arguments, j));

          ARR_APPEND(args, arg);
        }

        instantiate_theorem(state, ref->theorem, args, &proven_arr, TRUE);

        for (size_t j = 0; j < ARR_LENGTH(proven_arr); ++j)
        {
          Value *proven = *ARR_GET(proven_arr, j);
          char *proven_str = html_render_value(proven);
          char *proven_latex = latex_render_value(proven);
          char *proven_label;
          asprintf(&proven_label, "<li><code>%s</code><br />\\(%s\\)</li>\n",
            proven_str, proven_latex);
          fputs(proven_label, f);
          free(proven_str);
          free(proven_latex);
          free(proven_label);
        }
      }
      fputs("</ul>\n", f);
      fputs("</div></li>\n", f);
    }
    fputs("</ol>\n", f);
    fputs("</div>\n", f);
  }*/
  fputs("</div>\n", f);

  fputs("<a href=\"../index.html\">Index</a>", f);
  fputs(HTML_END, f);
  fclose(f);
  return 0;
}

int
render_html(const sl_LogicState *state, const char *output_dir)
{
  mkdir(output_dir, 0777); /* TODO: handle errors. */
  {
    char *style_dst, *style_src;
    asprintf(&style_dst, "%s/style.css", output_dir);
    asprintf(&style_src, "./res/style.css", style_src);
    sl_copy_file(style_dst, style_src);
    free(style_dst);
    free(style_src);
  }
  {
    char symbol_dir[1024];
    snprintf(symbol_dir, 1024, "%s/symbols", output_dir);
    mkdir(symbol_dir, 0777); /* TODO: handle errors. */
  }
  {
    char index_path[1024];
    snprintf(index_path, 1024, "%s/index.html", output_dir);
    int err = html_render_index_page(state, index_path);
    PROPAGATE_ERROR(err);
  }
  {
    char all_path[1024];
    snprintf(all_path, 1024, "%s/all.html", output_dir);
    int err = html_render_all_page(state, all_path);
    PROPAGATE_ERROR(err);
  }
  for (size_t i = 0; i < ARR_LENGTH(state->symbol_table); ++i)
  {
    const sl_LogicSymbol *sym = ARR_GET(state->symbol_table, i);
    char page_path[1024];
    if (sym->type == sl_LogicSymbolType_Theorem)
    {
      const struct Theorem *thm = (struct Theorem *)sym->object;
      snprintf(page_path, 1024, "%s/symbols/theorem-%zu.html",
        output_dir, thm->id);
      html_render_theorem_page(state, thm, page_path);
    }
    /*if (sym->type == SymbolTypeType)
      html_render_type((struct Type *)sym->object, f);
    else if (sym->type == SymbolTypeConstant)
      html_render_constant((struct Constant *)sym->object, f);
    else if (sym->type == SymbolTypeExpression)
      html_render_expression((struct Expression *)sym->object, f);*/
    /*if (sym->type == SymbolTypeTheorem)
      html_render_theorem_page((struct Theorem *)sym->object, f);*/
  }
  return 0;
}
