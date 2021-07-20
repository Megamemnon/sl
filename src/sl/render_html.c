#include "render.h"
#include "common.h"
#include <unistd.h>
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
  return magma_asprintf(HTML_HEAD_FORMAT, title);
}

int
render_index(const LogicState *state, const char *filepath)
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
    int err = render_index(state, index_path);
    PROPAGATE_ERROR(err);
  }
  return 0;
}
