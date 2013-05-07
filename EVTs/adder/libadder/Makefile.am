AUTOMAKE_OPTIONS = 1.8 dist-bzip2 gnits
EXTRA_DIST = BUGS \
	     THANKS \
	     VERSION \
	     autogen.sh \
	     debian/changelog \
	     debian/compat \
	     debian/control \
	     debian/copyright \
	     debian/docs \
	     debian/libadder0.files \
	     debian/libadder-dev.files \
	     debian/rules \
	     debian/shlibs.local
if BUILD_TESTS
SUBDIRS = src tests
else
SUBDIRS = src
endif
doc_DOCS = AUTHORS BUGS ChangeLog COPYING INSTALL NEWS README THANKS VERSION

DISTCLEANFILES = config.log config.status \
		*~ *.bak *.\#* src/*~ src/*.bak/src *.\#* \
		$(PACKAGE)-$(VERSION).tar.gz $(PACKAGE)-$(VERSION).tar.bz2

install-data-local:
	$(mkdir_p) $(DESTDIR)$(libdir)/pkgconfig
	$(INSTALL) -m 644 $(PACKAGE).pc $(DESTDIR)$(libdir)/pkgconfig
