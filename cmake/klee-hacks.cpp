#include <llvm/Support/CommandLine.h>

namespace klee {
llvm::cl::OptionCategory SolvingCat("Constraint solving options",
                              "These options impact constraint solving.");
}