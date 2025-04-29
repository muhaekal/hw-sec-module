# CMake generated Testfile for 
# Source directory: /home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/sysc/simple_perf
# Build directory: /home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/examples/sysc/simple_perf
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(_deps/systemc-src/examples/sysc/simple_perf/simple_perf "/usr/bin/cmake" "-DTEST_EXE=/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/bin/simple_perf" "-DTEST_DIR=/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/examples/sysc/simple_perf" "-DTEST_INPUT=" "-DTEST_GOLDEN=" "-DTEST_FILTER=" "-DDIFF_COMMAND=/usr/bin/diff" "-DDIFF_OPTIONS=-u" "-P" "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/cmake/run_test.cmake")
set_tests_properties(_deps/systemc-src/examples/sysc/simple_perf/simple_perf PROPERTIES  FAIL_REGULAR_EXPRESSION "^[*][*][*]ERROR" _BACKTRACE_TRIPLES "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/CMakeLists.txt;137;add_test;/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/sysc/simple_perf/CMakeLists.txt;44;configure_and_add_test;/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/sysc/simple_perf/CMakeLists.txt;0;")
