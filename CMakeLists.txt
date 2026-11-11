cmake_minimum_required(VERSION 3.16)
project(m68k_recomp_core LANGUAGES C)

include("${CMAKE_CURRENT_LIST_DIR}/cmake/M68kRecompCore.cmake")

# The frontend depends on consumer-owned image/configuration interfaces, so it
# is intentionally provided as a source package rather than a standalone
# library. Consumers call m68k_recomp_core_sources() and add the returned files
# to their recompiler executable.
add_library(m68k_recomp_core_headers INTERFACE)
target_include_directories(m68k_recomp_core_headers INTERFACE
    "${CMAKE_CURRENT_LIST_DIR}/common")

add_library(m68k_step_runtime STATIC runtime/m68k_step.c)
target_include_directories(m68k_step_runtime PUBLIC "${CMAKE_CURRENT_LIST_DIR}/runtime")
target_compile_features(m68k_step_runtime PUBLIC c_std_11)

if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    include(CTest)
    if(BUILD_TESTING)
        add_subdirectory(tests/step)
        add_subdirectory(tests/genesis)
    endif()
endif()

