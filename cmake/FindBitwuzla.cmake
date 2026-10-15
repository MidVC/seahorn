# - Try to find Bitwuzla (https://bitwuzla.github.io)
# Once done this will define
#  BITWUZLA_FOUND - System has Bitwuzla
#  BITWUZLA_INCLUDE_DIR - The directory containing bitwuzla/cpp/bitwuzla.h
#  BITWUZLA_LIBRARY - The Bitwuzla shared library
#  BITWUZLA_VERSION - The version, read from the bitwuzla.pc installed next
#                     to the library (unset if there is none)
#
# Only BITWUZLA_HOME is searched, never the default prefixes.

# Forget a previous result when BITWUZLA_HOME changes, so the cache does not
# keep a library from the old prefix.
if (NOT "${BITWUZLA_HOME}" STREQUAL "${_BITWUZLA_HOME_SEARCHED}")
  unset(BITWUZLA_INCLUDE_DIR CACHE)
  unset(BITWUZLA_LIBRARY CACHE)
endif()
set(_BITWUZLA_HOME_SEARCHED "${BITWUZLA_HOME}" CACHE INTERNAL "")

# SeaHorn puts .a first in CMAKE_FIND_LIBRARY_SUFFIXES. Ask for the shared
# library by its full name first.
set(_BITWUZLA_NAMES
  ${CMAKE_SHARED_LIBRARY_PREFIX}bitwuzla${CMAKE_SHARED_LIBRARY_SUFFIX} bitwuzla)

find_path(BITWUZLA_INCLUDE_DIR bitwuzla/cpp/bitwuzla.h
  PATHS "${BITWUZLA_HOME}/include" NO_DEFAULT_PATH)
# Meson may install into lib/<multiarch> on Debian and Ubuntu.
find_library(BITWUZLA_LIBRARY NAMES ${_BITWUZLA_NAMES}
  PATHS "${BITWUZLA_HOME}/lib" "${BITWUZLA_HOME}/lib64"
        "${BITWUZLA_HOME}/lib/${CMAKE_LIBRARY_ARCHITECTURE}"
  NO_DEFAULT_PATH)

# A static libbitwuzla.a (the default of Bitwuzla's configure.py) also needs
# libbitwuzla{ls,bv,bb}, the SAT solvers, GMP and MPFR. Only the shared
# library is supported.
if (BITWUZLA_LIBRARY MATCHES "\\${CMAKE_STATIC_LIBRARY_SUFFIX}$")
  message(WARNING "Ignoring static ${BITWUZLA_LIBRARY}: "
    "build Bitwuzla with ./configure.py --shared")
  unset(BITWUZLA_LIBRARY CACHE)
  set(BITWUZLA_LIBRARY BITWUZLA_LIBRARY-NOTFOUND)
endif()

unset(BITWUZLA_VERSION)
if (BITWUZLA_LIBRARY)
  get_filename_component(_BITWUZLA_LIBDIR "${BITWUZLA_LIBRARY}" DIRECTORY)
  if (EXISTS "${_BITWUZLA_LIBDIR}/pkgconfig/bitwuzla.pc")
    file(STRINGS "${_BITWUZLA_LIBDIR}/pkgconfig/bitwuzla.pc" _BITWUZLA_PC_VERSION
      REGEX "^Version:")
    string(REGEX REPLACE "^Version:[ \t]*" "" BITWUZLA_VERSION
      "${_BITWUZLA_PC_VERSION}")
  endif()
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Bitwuzla
  REQUIRED_VARS BITWUZLA_LIBRARY BITWUZLA_INCLUDE_DIR
  VERSION_VAR BITWUZLA_VERSION)

mark_as_advanced(BITWUZLA_INCLUDE_DIR BITWUZLA_LIBRARY)
