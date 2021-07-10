cmake_minimum_required(VERSION 3.10)
project(magma)

set(CMAKE_BUILD_TYPE Debug)

# Library
add_library(magma
  src/lib/arg.c
  src/lib/code.c
  src/lib/lex.c
  src/lib/parse.c
)

include_directories(
  src/lib
)


# Languages
## Asm
add_executable(asm
  src/asm/main.c

  src/asm/asm.c
)
target_link_libraries(asm
  magma
)

## gm
add_executable(gm
  src/gm/main.c

  src/gm/gm.c
)
target_link_libraries(gm
  magma
)

## sl
add_executable(sl
  src/sl/main.c

  src/sl/sl.c
)
target_link_libraries(sl
  magma
)

## Sol
add_executable(sol
  src/sol/main.c

  src/sol/sol.c
)
target_link_libraries(sol
  magma
)
