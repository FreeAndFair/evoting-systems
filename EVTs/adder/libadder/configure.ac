#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([libadder],[0.1.0],[adder@cse.uconn.edu])
AM_INIT_AUTOMAKE
AC_CONFIG_SRCDIR([src/misc.cpp])
AC_CONFIG_HEADER(config.h)

AC_PROG_CXX
AC_PROG_CC
AC_PROG_INSTALL
AC_PROG_MAKE_SET
AC_PROG_LIBTOOL
AC_CHECK_ENTROPY_SOURCE

# Checks for libraries.

AC_CHECK_LIB(gmp, __gmpz_init, , AC_MSG_ERROR(cannot find gmp))
AC_CHECK_LIB(ssl, SHA1, , AC_MSG_ERROR(cannot find OpenSSL))

AC_LANG_PUSH([C++])
AC_CHECK_LIB(boost_regex, main, , AC_MSG_ERROR(cannot find boost_regex))
AC_LANG_POP([])

# Checks for header files.
AC_HEADER_STDC
AC_CHECK_HEADERS([string.h sys/time.h])
AC_CHECK_HEADER(gmp.h, , AC_MSG_ERROR(cannot find GMP header))
AC_CHECK_HEADER(openssl/sha.h, , AC_MSG_ERROR(cannot find OpenSSL header))
AC_CHECK_HEADER(boost/regex.hpp, , AC_MSG_ERROR(cannot find Boost Regex header))

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_C_CONST
AC_TYPE_SIZE_T
AC_CXX_EXCEPTIONS

# Checks for library functions.
AC_CHECK_FUNCS([memset])

# Script options
AC_ARG_ENABLE([armor],
  AS_HELP_STRING(--enable-armor,enable armor),
[armor="$enableval"; CXXFLAGS="$CXXFLAGS -DARMOR"],
[armor="no"])

AC_MSG_CHECKING(whether to enable armor)
if test "x$armor" = xyes; then
    AC_MSG_RESULT(yes)
else
    AC_MSG_RESULT(no)
fi

AM_CONDITIONAL(ARMOR, test "x$armor" != xno)

AC_ARG_ENABLE([tests],
  AS_HELP_STRING(--disable-tests,disable building of tests),
[build_tests="$enableval"],
[build_tests="yes"])

AC_MSG_CHECKING(whether to enable tests)
if test "x$build_tests" = xyes; then
    AC_MSG_RESULT(yes)
else
    AC_MSG_RESULT(no)
fi

AM_CONDITIONAL(BUILD_TESTS, test "x$build_tests" != xno)

AC_ARG_ENABLE(apidoc,
  AS_HELP_STRING(--enable-apidoc, enable building of API documentation with doxygen),
  [ENABLE_DOXYGEN="$enableval"],
  [ENABLE_DOXYGEN="no"])

AC_ARG_WITH(latexdir,
  AS_HELP_STRING(--with-latexdir=DIR, specify path to LaTeX installation),
  [LATEX_HOME="$withval"],
  [LATEX_HOME=""])

AC_MSG_CHECKING(whether to build API documentation)
AC_MSG_RESULT($ENABLE_DOXYGEN)
if test "x$ENABLE_DOXYGEN" != xno; then
  AC_CHECK_PROG(LATEX, latex, latex, no)
  AC_MSG_CHECKING(for latex home)
  if test "x$LATEX_HOME" = x; then
    LATEX_HOME=/usr/share/texmf/tex/latex
  fi
  AC_MSG_RESULT($LATEX_HOME)
  AC_SUBST(LATEX_HOME)

  AC_CHECK_PROG(DOXYGEN, doxygen, doxygen, no)
  AC_CHECK_PROG(DOT, dot, dot, no)
  AC_CHECK_PROG(DVIPS, dvips, dvips, no)
  AC_CHECK_PROG(GS, gs, gs, no)
  AC_CHECK_FILES($LATEX_HOME/amsfonts/amsfonts.sty
                 $LATEX_HOME/amsmath/amsmath.sty
                 $LATEX_HOME/amsfonts/amssymb.sty, , AMSPKGS="no")
fi

test "x$ENABLE_DOXYGEN" != xno \
&& test "x$DOXYGEN" != xno \
&& test "x$DOT" != xno \
&& test "x$DVIPS" != xno \
&& test "x$GS" != xno \
&& test "x$LATEX" != xno \
&& test -d "$LATEX_HOME" \
&& test "x$AMSPKGS" != xno \
&& HAVE_DOXYGEN=yes \
|| HAVE_DOXYGEN=no
AM_CONDITIONAL(HAVE_DOXYGEN, test "x$HAVE_DOXYGEN" != xno)
if test "x$ENABLE_DOXYGEN" != xno; then
  if test "x$HAVE_DOXYGEN" = xno; then
    AC_MSG_WARN([configure has opted to build API documentation, but could not find all of the required dependencies])
  fi
fi

AC_CONFIG_FILES([Makefile
                 libadder.pc
                 libadder.spec
                 src/Doxyfile
                 src/Makefile
                 tests/Makefile])
AC_OUTPUT
