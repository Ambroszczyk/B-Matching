cmake_minimum_required (VERSION 3.8)
project (adorate)

find_package ( Threads REQUIRED )

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_FLAGS "-o3")

# http://stackoverflow.com/questions/10555706/
macro (add_executable _name)
    # invoke built-in add_executable
    _add_executable(${ARGV})
    if (TARGET ${_name})
        target_link_libraries(${_name} ${CMAKE_THREAD_LIBS_INIT} )
    endif()
endmacro()

add_executable(adorate main.cpp blimit.cpp blimit.hpp)
