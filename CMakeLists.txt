cmake_minimum_required(VERSION 3.10)
project(magma)

set(SOURCES
  src/main.c

  src/c-lang.c
  src/parse.c
)

add_executable(magma ${SOURCES})
