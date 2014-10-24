cmake_minimum_required(VERSION 2.8)

project(tosearch)

add_definitions(-DNAUTY_PATH="${NAUTY_PATH}")
add_compile_options(-std=c++0x)
add_executable(tosearch main.cpp)

install(TARGETS tosearch RUNTIME DESTINATION bin)
