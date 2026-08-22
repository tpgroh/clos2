cmake_minimum_required(VERSION 3.25 FATAL_ERROR)
project(clos2)

if(NOT COMMAND add_mim_plugin)
    find_package(mim REQUIRED)
endif()

add_mim_plugin(clos2
    SOURCES
        src/clos2.cpp
        src/normalizers.cpp
    INSTALL
)

if(MIM_BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()

if (BUILD_TESTING)
    add_subdirectory(gtest)
endif()
