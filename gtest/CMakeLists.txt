add_executable(clos2-internals-gtest)
target_sources(clos2-internals-gtest
    PRIVATE
        internals.cpp
)
target_include_directories(clos2-internals-gtest PUBLIC ../include/)
target_link_libraries(clos2-internals-gtest
    PRIVATE
        gtest_main
        libmim
)
add_dependencies(clos2-internals-gtest mim_all_plugins)
gtest_discover_tests(clos2-internals-gtest
    TEST_PREFIX "clos2."
    DISCOVERY_TIMEOUT 60
)

add_dependencies(mim_all
    clos2-internals-gtest
)
