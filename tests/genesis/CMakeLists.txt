add_executable(m68k_return_capture_test
    return_capture_test.c
    ../../common/m68k_decoder.c
    ../../profiles/genesis/return_capture.c)
target_include_directories(m68k_return_capture_test PRIVATE
    . ../../common ../../profiles/genesis)
target_compile_features(m68k_return_capture_test PRIVATE c_std_11)
if(MSVC)
    target_compile_options(m68k_return_capture_test PRIVATE /W4 /WX)
else()
    target_compile_options(m68k_return_capture_test PRIVATE -Wall -Wextra -Werror)
endif()
add_test(NAME m68k_return_capture COMMAND m68k_return_capture_test)
