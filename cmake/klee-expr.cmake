file(GLOB klee_EXPR_SOURCES "${klee_SOURCE_DIR}/lib/Expr/*.cpp")
target_sources(${CMKR_TARGET} PRIVATE
    ${klee_EXPR_SOURCES}
    ${CMAKE_CURRENT_LIST_DIR}/klee-hacks.cpp
)
