cmake_minimum_required(VERSION 3.10)
project(magma)

set(SOURCES
  src/main.c

  src/asm-lang.c
  src/c-lang.c
  src/lex.c
  src/sol-lang.c
)

if(APPLE)
  list(APPEND
    SOURCES
    src/mach-o.c
  )
endif()

add_executable(magma ${SOURCES})
