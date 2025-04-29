# CMake generated Testfile for 
# Source directory: /home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/sysc/rsa
# Build directory: /home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/examples/sysc/rsa
# 
# This file includes the relevant testing commands required for 
# testing this directory and lists subdirectories to be tested as well.
add_test(_deps/systemc-src/examples/sysc/rsa/rsa "/usr/bin/cmake" "-DTEST_EXE=/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/bin/rsa" "-DTEST_DIR=/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/examples/sysc/rsa" "-DTEST_INPUT=" "-DTEST_GOLDEN=" "-DTEST_FILTER=" "-DDIFF_COMMAND=/usr/bin/diff" "-DDIFF_OPTIONS=-u" "-P" "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/cmake/run_test.cmake")
set_tests_properties(_deps/systemc-src/examples/sysc/rsa/rsa PROPERTIES  FAIL_REGULAR_EXPRESSION "^[*][*][*]ERROR" _BACKTRACE_TRIPLES "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/CMakeLists.txt;137;add_test;/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/sysc/rsa/CMakeLists.txt;44;configure_and_add_test;/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/examples/sysc/rsa/CMakeLists.txt;0;")
