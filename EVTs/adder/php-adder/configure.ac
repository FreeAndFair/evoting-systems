#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.59)
AC_INIT([php-adder],[0.1.0],[adder@cse.uconn.edu])
AM_INIT_AUTOMAKE
AC_CONFIG_SRCDIR([share/adder_interface.php])

# Checks for programs.
AC_PROG_INSTALL
AC_PROG_MAKE_SET

# Checks for libraries.

# Checks for header files.

# Checks for typedefs, structures, and compiler characteristics.

# Checks for library functions.

# Script options
AC_ARG_WITH(wwwrootdir,
  AS_HELP_STRING(--with-wwwrootdir, specify WWW root directory),
  [WWWROOTDIR="$withval"],
  [WWWROOTDIR="/var/www"])

AC_MSG_CHECKING(for WWW root directory)
AC_MSG_RESULT($WWWROOTDIR)
AC_SUBST(WWWROOTDIR)

AC_CONFIG_FILES([Makefile
                 php-adder.spec
                 etc/Makefile
                 log/Makefile
                 share/Makefile
                 var/Makefile
                 www/Makefile
                 www/images/Makefile
                 www/scripts/Makefile
                 www/stylesheets/Makefile ])
AC_OUTPUT
