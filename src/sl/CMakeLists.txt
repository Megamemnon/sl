set(SOURCES
  logic.c
  render_html.c
  render_latex.c
  sl.c
)

# Main executable
add_executable(sl
  main.c

  ${SOURCES}
)
target_link_libraries(sl
  magma
)

# Tests
add_executable(test_sl
  tests/test.c

  ${SOURCES}
)
target_link_libraries(test_sl
  magma
)
add_test(sl test_sl)
