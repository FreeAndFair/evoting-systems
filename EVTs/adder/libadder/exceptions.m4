AC_DEFUN([AC_CXX_EXCEPTIONS],
[AC_PREREQ(2.59)dnl
AC_CACHE_CHECK(whether C++ compiler supports exceptions, ac_cv_cxx_exceptions,
[AC_LANG_PUSH([C++])
AC_TRY_COMPILE(, [try {
    throw  "Trying to catch exception";
} catch (char*) {
    return 1;
}], ac_cv_cxx_exceptions="yes", ac_cv_cxx_exceptions="no")
AC_LANG_POP([])

if test "x$ac_cv_cxx_exceptions" != xyes; then
  AC_MSG_ERROR([C++ compiler does not support exceptions])
else
  test "x$GXX" = xyes && CXXFLAGS="$CXXFLAGS -fexceptions"
fi])
])
