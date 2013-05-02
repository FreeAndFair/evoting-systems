INCLUDES = -I$(top_srcdir)/src
LDADD = $(top_builddir)/src/libadder.la

if BUILD_TESTS
TESTS = addertest sha1test #keytest polytest inttest newzkptest
if ARMOR
enctest_SOURCES = enctest.cpp
TESTS += enctest
endif
addertest_SOURCES = addertest.cpp
#inttest_SOURCES = inttest.cpp
#keytest_SOURCES = keytest.cpp
#polytest_SOURCES = polytest.cpp
#newzkptest_SOURCES = newzkptest.cpp
sha1test_SOURCES = sha1test.cpp
noinst_PROGRAMS = $(TESTS)
endif
