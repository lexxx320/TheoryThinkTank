cmake_minimum_required(VERSION 2.8)

project(inducedgraphs)

add_compile_options(-std=c++0x)
add_executable(inducedgraphs main.cpp)
target_link_libraries(inducedgraphs boost_program_options)

install(TARGETS inducedgraphs RUNTIME DESTINATION bin)
