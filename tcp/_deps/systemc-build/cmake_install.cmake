# Install script for directory: /home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/opt/systemc")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xdocx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/share/doc/systemc" TYPE FILE FILES
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/AUTHORS"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/ChangeLog"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/INSTALL"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/cmake/INSTALL_USING_CMAKE"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/LICENSE"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/NEWS"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/NOTICE"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/README"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-src/RELEASENOTES"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xdevx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage/SystemCLanguageTargets.cmake")
    file(DIFFERENT EXPORT_FILE_CHANGED FILES
         "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage/SystemCLanguageTargets.cmake"
         "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/CMakeFiles/Export/lib/cmake/SystemCLanguage/SystemCLanguageTargets.cmake")
    if(EXPORT_FILE_CHANGED)
      file(GLOB OLD_CONFIG_FILES "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage/SystemCLanguageTargets-*.cmake")
      if(OLD_CONFIG_FILES)
        message(STATUS "Old export file \"$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage/SystemCLanguageTargets.cmake\" will be replaced.  Removing files [${OLD_CONFIG_FILES}].")
        file(REMOVE ${OLD_CONFIG_FILES})
      endif()
    endif()
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage" TYPE FILE FILES "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/CMakeFiles/Export/lib/cmake/SystemCLanguage/SystemCLanguageTargets.cmake")
  if("${CMAKE_INSTALL_CONFIG_NAME}" MATCHES "^([Rr][Ee][Ll][Ee][Aa][Ss][Ee])$")
    file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage" TYPE FILE FILES "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/CMakeFiles/Export/lib/cmake/SystemCLanguage/SystemCLanguageTargets-release.cmake")
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xdevx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCLanguage" TYPE FILE FILES
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/SystemCLanguageConfig.cmake"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/SystemCLanguageConfigVersion.cmake"
    )
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xdevx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/SystemCTLM" TYPE FILE FILES
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/SystemCTLMConfig.cmake"
    "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/SystemCTLMConfigVersion.cmake"
    )
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/docs/cmake_install.cmake")
  include("/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/_deps/systemc-build/src/cmake_install.cmake")

endif()

