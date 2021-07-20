cmake_minimum_required(VERSION 3.10)
project(sl)
enable_testing()

set(CMAKE_BUILD_TYPE Debug)

# Library
add_library(sl
  src/arg.c
  src/common.c
  src/lex.c
  src/logic.c
  src/parse.c
  src/render_html.c
  src/render_latex.c
  src/sl.c
)

# Main executable
add_executable(sl_bin src/main.c)
target_link_libraries(sl_bin sl)
set_target_properties(sl_bin PROPERTIES OUTPUT_NAME sl)

# Tests
add_executable(test_sl tests/test.c)
target_link_libraries(test_sl sl)
add_test(sl test_sl)
