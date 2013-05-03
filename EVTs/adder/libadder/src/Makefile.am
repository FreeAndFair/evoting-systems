EXTRA_DIST = config-win32.h \
			 libadder.sln \
			 libadder.vcproj

lib_LTLIBRARIES = libadder.la
libadder_la_SOURCES = Integer.cpp \
		      misc.cpp \
		      radix64.cpp \
		      Vote.cpp \
		      PublicKey.cpp \
	              PrivateKey.cpp \
		      Context.cpp \
		      Polynomial.cpp \
		      ElgamalCiphertext.cpp \
	              MembershipProof.cpp \
	              VoteProof.cpp

pkginclude_HEADERS = Integer.h \
		     misc.h \
		     radix64.h \
		     libadder.h \
		     Vote.h \
		     PublicKey.h \
	             PrivateKey.h \
	             Context.h \
	             common.h \
	             exceptions.h \
	             Polynomial.h \
		     ElgamalCiphertext.h \
	             MembershipProof.h \
	             VoteProof.h

pkgincludedir = $(includedir)/libadder

docdir = $(datadir)/doc/$(PACKAGE_NAME)

if HAVE_DOXYGEN
all-local: api

api: stamp-doxygen

stamp-doxygen: Doxyfile $(HEADERS) $(SOURCES)
	$(DOXYGEN)
	rm -f stamp-doxygen
	touch stamp-doxygen

install-data-local:
	$(mkdir_p) $(DESTDIR)$(docdir)
	cp -pR html $(DESTDIR)$(docdir)

uninstall-local:
	rm -rf $(DESTDIR)$(docdir)

distclean-local:
	-rm -rf html
endif

maintainer-clean-local:
	-rm -f Makefile.in
