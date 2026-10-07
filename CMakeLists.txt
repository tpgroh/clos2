cmake_minimum_required(VERSION 3.25 FATAL_ERROR)
project(clos2)

if(NOT COMMAND add_mim_plugin)
    find_package(mim REQUIRED)
endif()

add_mim_plugin(clos2
    SOURCES
        src/clos2.cpp
        src/normalizers.cpp
        src/closure.cpp
        src/phase/clos_conv.cpp
        src/phase/lam_lift_type.cpp
        src/phase/hoist_up.cpp
)

if(MIM_BUILD_EXAMPLES)
    add_subdirectory(examples)
endif()
