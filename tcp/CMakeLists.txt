# +---------------------------------------------------+
# | Copyright (c) LUBIS EDA GmbH, all rights reserved |
# | Created on 22.02.2025 at 10:07                    |
# | Contact: contact@lubis-eda.com                    |
# | Author: Tobias Ludwig, Michael Schwarz            |
# +---------------------------------------------------+


########################## Configuration ##########################

# Set the path to the directory where the 'Interfaces.h' header can be found
set(INTERFACES_DIR "home/muhammad-haekal/.vscode-server/extensions/lubis-eda.lubis-vsc-plugin-1.0.0/DeSCAM/include/interfaces")
# Set the path to the directory where the original module files can be found
set(MODULES_DIR "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp")
# Set TRUE if this CMakeLists should download and install SystemC by itself,
# otherwise set to FALSE and give a directory path to another SystemC installation
set(INSTALL_SYSTEMC TRUE)
set(SYSTEMC_INCLUDE_DIR "")
set(SYSTEMC_LIB_DIR "")

###################################################################

include(FetchContent)

cmake_minimum_required(VERSION 3.10)
project(LUBIS_Simulation)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/bin)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/lib)

if(INSTALL_SYSTEMC)
  FetchContent_Declare(SYSTEMC
    GIT_REPOSITORY https://github.com/accellera-official/systemc
    GIT_TAG 2.3.3
    GIT_SHALLOW TRUE
    GIT_PROGRESS TRUE
  )
  FetchContent_MakeAvailable(SYSTEMC)
  include_directories(
    ${CMAKE_CACHEFILE_DIR}/_deps/systemc-src/src
  )
else()
  include_directories(
    ${SYSTEMC_INCLUDE_DIR}
  )
  link_directories(
    ${SYSTEMC_LIB_DIR}
  )
endif()

include_directories(
  ${INTERFACES_DIR}
  ${MODULES_DIR}
)

add_executable(tcp_server_tests
  tcp_server_main.cpp
)
target_link_libraries(tcp_server_tests PRIVATE
  systemc
)
