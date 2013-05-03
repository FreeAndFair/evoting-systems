AC_DEFUN([AC_CHECK_ENTROPY_SOURCE],
[AC_PREREQ(2.59)dnl
AC_MSG_CHECKING(for entropy source)
ENTROPY_SOURCE="no"
if test -c /dev/random; then
  ENTROPY_SOURCE="/dev/random"
elif test -c /dev/srandom; then
  ENTROPY_SOURCE="/dev/srandom"
elif test -c /dev/urandom; then
  ENTROPY_SOURCE="/dev/urandom"
elif test -c /dev/prandom; then
  ENTROPY_SOURCE="/dev/prandom"
fi

AC_MSG_RESULT($ENTROPY_SOURCE)

if test x"$ENTROPY_SOURCE" != x"no"; then
  if test x"$ENTROPY_SOURCE" != x"/dev/random" -a x"$ENTROPY_SOURCE" != x"/dev/srandom"; then
      AC_MSG_WARN(entropy device may not be strong)
  fi
  AC_DEFINE(HAVE_ENTROPY_DEVICE, 1, [defined if the entropy source is a device])
  AC_DEFINE_UNQUOTED(ENTROPY_SOURCE, "$ENTROPY_SOURCE", [defined to the name of the entropy source])
else
  AC_DEFINE(HAVE_ENTROPY_DEVICE, 0, [defined if the entropy source is a device])
  AC_CHECK_FUNC(rand, , AC_MSG_ERROR(cannot find entropy source))
fi
])
