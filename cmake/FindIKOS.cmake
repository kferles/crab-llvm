if (NOT IKOS_FOUND)
  set (IKOS_ROOT "" CACHE PATH "Search path for ikos-core")
  message (STATUS "Ikos root: ${IKOS_ROOT}")
  find_path(IKOS_INCLUDE_DIR NAMES ikos/cfg/Cfg.hpp
    PATHS ${IKOS_ROOT}/include  NO_DEFAULT_PATH)
  find_library(IKOS_DBM_LIB NAMES dbm PATHS ${IKOS_ROOT}/lib NO_DEFAULT_PATH)
  message (STATUS "IKOS_DBM_LIB: ${IKOS_DBM_LIB}")
  
  include (FindPackageHandleStandardArgs)
  find_package_handle_standard_args(IKOS REQUIRED_VARS IKOS_INCLUDE_DIR) 
  mark_as_advanced(IKOS_ROOT IKOS_INCLUDE_DIR IKOS_DBM_LIB)
  message (STATUS "Found Ikos at ${IKOS_INCLUDE_DIR}")
  # start from 1 to make cmakedefine happy
  set (IKOS_MAJOR_VERSION 1)
  if (IKOS_DBM_LIB)
    set (IKOS_MINOR_VERSION 2)
  else()
    set (IKOS_MINOR_VERSION 1)
    set (IKOS_DBM_LIB CACHE FILEPATH "" FORCE)
  endif()
endif()
