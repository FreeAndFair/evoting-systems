# -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([cryptoserver],[0.1.0],[adder@cse.uconn.edu])

AM_INIT_AUTOMAKE(cryptoserver, 0.1.0)
AC_CONFIG_SRCDIR([src/main.cc])
AC_CONFIG_HEADER([config.h])

# Script options
AC_ARG_ENABLE(ssl,
  AS_HELP_STRING(--disable-ssl, disable use of SSL),
  [ENABLE_SSL="$enableval"],
  [ENABLE_SSL="yes"])

test "x$prefix" = xNONE && prefix=$ac_default_prefix
test "x$exec_prefix" = xNONE && exec_prefix='${prefix}'

# Checks for programs.
AC_PROG_CXX
AC_PROG_CC

AC_CHECK_PROG(MYSQL_CONFIG, mysql_config, mysql_config, no)
if test "x$MYSQL_CONFIG" = xno; then
  AC_MSG_ERROR(cannot find mysql_config)
else
  CPPFLAGS="$CPPFLAGS `$MYSQL_CONFIG --cflags`"
  LIBS="$LIBS `$MYSQL_CONFIG --libs`"
fi

# Checks for header files.
AC_HEADER_STDC
AC_CHECK_HEADERS([stdlib.h sys/types.h unistd.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_HEADER_STDBOOL
AC_C_CONST
AC_CXX_EXCEPTIONS

# Checks for libraries.
AC_CHECK_FUNCS(daemon)

AC_CHECK_HEADER(popt.h, , AC_MSG_ERROR(cannot find popt headers))
AC_CHECK_LIB(popt, poptGetContext, , AC_MSG_ERROR(cannot find popt library))

AC_LANG_PUSH([C++])
CPPFLAGS="$CPPFLAGS -I/usr/include/sqlplus -I/usr/include/sqlplus/mysql++ -I/usr/include/mysql++"
AC_CHECK_HEADER(mysql++.h, , AC_MSG_ERROR(cannot find MySQL++ header))
AC_CHECK_LIB(mysqlpp, main, , AC_MSG_ERROR(cannot find MySQL++ library))

AC_CHECK_HEADER(boost/spirit/core.hpp, , AC_MSG_ERROR(cannot find Boost Spirit header))

AC_CHECK_HEADER(boost/regex.hpp, , AC_MSG_ERROR(cannot find Boost Regex header))
AC_CHECK_LIB(boost_regex, main, , AC_MSG_ERROR(cannot find boost_regex))
AC_LANG_POP([])

PKG_CHECK_MODULES(ACE, ACE >= 5.4.7, , AC_MSG_ERROR(cannot find ACE))
AC_MSG_CHECKING(whether to enable SSL)
AC_MSG_RESULT($ENABLE_SSL)
if test "x$ENABLE_SSL" != xno; then
  CPPFLAGS="$CPPFLAGS -DENABLE_SSL"
  PKG_CHECK_MODULES(ACE_SSL, ACE_SSL >= 5.4.7, , AC_MSG_ERROR(cannot find ACE_SSL))
fi

AC_SUBST(ACE_LIBS)
AC_SUBST(ACE_CFLAGS)

AC_SUBST(ACE_SSL_LIBS)
AC_SUBST(ACE_SSL_CFLAGS)

#PKG_CHECK_MODULES(LIBADDER, libadder >= 0.0.1, , AC_MSG_ERROR(cannot find libadder >= 0.0.1))
CXXFLAGS="$CXXFLAGS `pkg-config --cflags libadder`" LIBS="$LIBS `pkg-config --libs libadder`"
AC_SUBST(LIBADDER_CFLAGS)
AC_SUBST(LIBADDER_LIBS)

# Checks for library functions.

SYSCONFDIR=`eval echo ${sysconfdir}`
AC_SUBST(SYSCONFDIR)

AC_DEFINE_UNQUOTED(CONFIG_FILE, "`eval echo "${sysconfdir}/cryptoserver.conf"`", Define the config file here.)
AC_DEFINE_UNQUOTED(PID_FILE, "`eval echo "${localstatedir}/run/cryptoserver.pid"`", Define the pid file here.)

AC_CONFIG_FILES([cryptoserver.8
                 cryptoserver.conf.5
                 cryptoserver.init
                 cryptoserver.spec
                 Makefile
                 src/Makefile])

AC_OUTPUT
