cmake_minimum_required(VERSION 3.10)
project(magma)

# Library
add_library(magma
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

## Sol
add_executable(sol
  src/sol/main.c

  src/sol/sol.c
)
target_link_libraries(sol
  magma
)
