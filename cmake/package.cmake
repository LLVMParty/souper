# Installation

set(PACKAGE_NAME "${PROJECT_NAME}")
set(PACKAGE_DEPENDENCIES Z3 Alive2 hiredis LLVM-Wrapper)

# Copy targets
install(TARGETS souper EXPORT ${PACKAGE_NAME}Targets
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
  RUNTIME DESTINATION bin
  INCLUDES DESTINATION include
)

# Copy headers
install(DIRECTORY "${klee_SOURCE_DIR}/include/" DESTINATION include FILES_MATCHING PATTERN "*.h")
install(DIRECTORY "${CMAKE_SOURCE_DIR}/include/" DESTINATION include FILES_MATCHING PATTERN "*.h")
install(DIRECTORY "${CMAKE_BINARY_DIR}/include/" DESTINATION include FILES_MATCHING PATTERN "*.h")

include(CMakePackageConfigHelpers)
write_basic_package_version_file(
  "${CMAKE_CURRENT_BINARY_DIR}/${PACKAGE_NAME}/${PACKAGE_NAME}ConfigVersion.cmake"
  VERSION ${PROJECT_VERSION}
  COMPATIBILITY AnyNewerVersion
)

export(EXPORT ${PACKAGE_NAME}Targets
  FILE "${CMAKE_CURRENT_BINARY_DIR}/${PACKAGE_NAME}/${PACKAGE_NAME}Targets.cmake"
  #NAMESPACE Upstream::
)
configure_file(cmake/PackageConfig.cmake.in
  "${CMAKE_CURRENT_BINARY_DIR}/${PACKAGE_NAME}/${PACKAGE_NAME}Config.cmake"
  @ONLY
)

set(ConfigPackageLocation lib/cmake/${PACKAGE_NAME})
install(EXPORT ${PACKAGE_NAME}Targets
  FILE
  ${PACKAGE_NAME}Targets.cmake
  #NAMESPACE
  #  Upstream::
  DESTINATION
    ${ConfigPackageLocation}
)
install(
  FILES
    "${CMAKE_CURRENT_BINARY_DIR}/${PACKAGE_NAME}/${PACKAGE_NAME}Config.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/${PACKAGE_NAME}/${PACKAGE_NAME}ConfigVersion.cmake"
  DESTINATION
    ${ConfigPackageLocation}
)