cmake_minimum_required(VERSION 3.27)

project(glucose LANGUAGES CXX CUDA)
set( CMAKE_VERBOSE_MAKEFILE on )

option(BUILD_SHARED_LIBS OFF "True for building shared object")

# Dependencies {{{
find_package(ZLIB REQUIRED)
find_package(Threads REQUIRED)
# }}}

set(CMAKE_CXX_STANDARD 14)
set(main_simp "simp/Main.cc")
set(main_parallel "parallel/Main.cc")


# Basic Library
file(GLOB lib_srcs RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} mtl/*.cc core/*.cc simp/*.cc utils/*.cc simp/*.cu core/*.cu)
list(REMOVE_ITEM lib_srcs ${main_simp} ${main_parallel})

message(${lib_srcs})


if(BUILD_SHARED_LIBS)
    set(lib_type "SHARED")
else()
    set(lib_type "STATIC")
endif()

#link_libraries(${ZLIB_LIBRARY})

# base library
add_library(glucose ${lib_type} ${lib_srcs})
# Cuda stuff

target_compile_options(glucose PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:-lineinfo>)
target_include_directories(glucose PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
#target_include_directories(glucose PRIVATE ${CMAKE_CUDA_TOOLKIT_INCLUDE_DIRECTORIES})
#target_include_directories(glucose PRIVATE "/home/ostrowski/miniforge3/envs/gcc12/include")

set(CMAKE_CUDA_ARCHITECTURES 86)

#set_target_properties( glucose PROPERTIES CUDA_SEPARABLE_COMPILATION ON)
set_target_properties( glucose PROPERTIES CUDA_RESOLVE_DEVICE_SYMBOLS ON)
set_target_properties( glucose PROPERTIES CUDA_ARCHITECTURES "86")

add_executable(glucose-simp ${main_simp})
target_include_directories(glucose-simp PUBLIC ${ZLIB_INCLUDE_DIR})
target_link_libraries(glucose-simp PUBLIC ${ZLIB_LIBRARY} glucose)
