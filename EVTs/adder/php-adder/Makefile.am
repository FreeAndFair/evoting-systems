AUTOMAKE_OPTIONS = 1.9 dist-bzip2 gnits
EXTRA_DIST = BUGS \
	     VERSION \
	     autogen.sh \
	     debian/changelog \
	     debian/compat \
	     debian/control \
	     debian/copyright \
	     debian/dirs \
	     debian/rules
SUBDIRS = etc log share var www
doc_DOCS = AUTHORS BUGS ChangeLog COPYING INSTALL NEWS README THANKS TODO VERSION
DISTCLEANFILES = config.log config.status \
		*~ *.bak *.\#* src/*~ src/*.bak/src *.\#* \
		$(PACKAGE)-$(VERSION).tar.gz $(PACKAGE)-$(VERSION).tar.bz2
