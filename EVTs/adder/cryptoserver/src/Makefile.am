EXTRA_DIST = $(PACKAGE_NAME).conf.ex

sbin_PROGRAMS = cryptoserver

cryptoserver_SOURCES = ClientHandler.cc \
		       ClientHandler.hh \
		       Database.cc \
	               Database.hh \
		       ElectionTimeoutHandler.hh \
		       DecryptionHandler.hh \
	               main.cc \
		       Options.cc \
		       Options.hh \
		       Utilities.cc \
		       Utilities.hh

INCLUDES = $(ACE_CFLAGS) $(ACE_SSL_CFLAGS) $(LIBADDER_CFLAGS)
LIBS = @LIBS@ $(ACE_LIBS) $(ACE_SSL_LIBS) $(LIBADDER_LIBS)
