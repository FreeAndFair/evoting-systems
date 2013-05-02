AUTOMAKE_OPTIONS = 1.8 dist-bzip2 gnits

EXTRA_DIST = autogen.sh \
	     $(PACKAGE_NAME).init \
	     database/INSTALL.mysql \
	     database/permissions.sql \
	     database/schema.sql \
	     database/test-data.sql \
	     debian/changelog \
	     debian/compat \
	     debian/control \
	     debian/copyright \
             debian/cryptoserver-default \
	     debian/docs \
	     debian/init.d \
	     debian/rules

SUBDIRS = src
doc_DOCS = AUTHORS ChangeLog COPYING INSTALL NEWS README TODO
man_MANS = $(PACKAGE_NAME).8 $(PACKAGE_NAME).conf.5

install-data-local:
	$(INSTALL) -d -m 755 $(DESTDIR)$(sysconfdir)
	$(INSTALL) -m 644 $(top_srcdir)/src/$(PACKAGE_NAME).conf.ex $(DESTDIR)$(sysconfdir)/$(PACKAGE_NAME).conf
	$(INSTALL) -d -m 755 $(DESTDIR)$(mandir)/man8
	$(INSTALL) -m 644 $(PACKAGE_NAME).8 $(DESTDIR)$(mandir)/man8/$(PACKAGE_NAME).8
	$(INSTALL) -d -m 755 $(DESTDIR)$(mandir)/man5
	$(INSTALL) -m 644 $(PACKAGE_NAME).conf.5 $(DESTDIR)$(mandir)/man5/$(PACKAGE_NAME).conf.5

