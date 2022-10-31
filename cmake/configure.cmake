set(CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

configure_file(${CMAKE_SOURCE_DIR}/include/souper/Tool/GetSolver.h.in ${CMAKE_BINARY_DIR}/include/souper/Tool/GetSolver.h @ONLY)
configure_file(${CMAKE_SOURCE_DIR}/include/souper/KVStore/KVSocket.h.in ${CMAKE_BINARY_DIR}/include/souper/KVStore/KVSocket.h @ONLY)