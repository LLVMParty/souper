target_sources(${CMKR_TARGET} PRIVATE
    "${klee_SOURCE_DIR}/lib/Expr/Constraints.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/ExprBuilder.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/Expr.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/ExprEvaluator.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/ExprPPrinter.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/ExprSMTLIBPrinter.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/ExprUtil.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/ExprVisitor.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/Lexer.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/Parser.cpp"
    "${klee_SOURCE_DIR}/lib/Expr/Updates.cpp"
)