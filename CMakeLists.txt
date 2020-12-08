cmake_minimum_required( VERSION 2.8)

if (NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

set(CMAKE_CXX_FLAGS "-Wall -Wextra")
set(CMAKE_CXX_FLAGS_DEBUG "-g")
set(CMAKE_CXX_FLAGS_RELEASE "-O3")

project(modulate)

file(GLOB SOURCES "*.cpp")

add_executable(nksat ${SOURCES})

