/*  CryptoServer - secure online voting server
    Copyright (C) 2004  The Adder Team

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

/**
 * @file main.cc
 * Contains main program routines.
 */
#include <stdlib.h>
#include <sys/types.h>
#include <unistd.h>

#include <fstream>
#include <string>
#include <vector>

#include "ace/Acceptor.h"
#include "ace/Signal.h"
#include "ace/UUID.h"
#ifdef ENABLE_SSL
#include "ace/SSL/sslconf.h"
#include "ace/SSL/SSL_SOCK_Acceptor.h"
#else
#include "ace/SOCK_Acceptor.h"
#endif

#include "ClientHandler.hh"
#include "Options.hh"

#include "popt.h"

#undef VERSION
#undef VERSION
#undef PACKAGE
#undef PACKAGE_BUGREPORT
#undef PACKAGE_NAME
#undef PACKAGE_STRING
#undef PACKAGE_TARNAME
#undef PACKAGE_VERSION
#include "config.h"

int got_sighup = 0;

#ifdef ENABLE_SSL
template class ACE_Acceptor<ClientHandler, ACE_SSL_SOCK_ACCEPTOR>;
template class ACE_Svc_Handler<ACE_SSL_SOCK_STREAM, ACE_NULL_SYNCH>;
#else
template class ACE_Acceptor<ClientHandler, ACE_SOCK_ACCEPTOR>;
template class ACE_Svc_Handler<ACE_SOCK_STREAM, ACE_NULL_SYNCH>;
#endif

/**
 * Signal handler for the SIGINT signal.
 * @param i unused parameter for signal handlers.
 */
extern "C" void sigint_handler(int i)
{
    ACE_UNUSED_ARG(i);

    /* Print shutdown message. */
    ACE_DEBUG((LM_SHUTDOWN, "got sigint... shutting down server daemon\n"));

    ACE_OS::exit(0);
}

extern "C" void sighup_handler(int i)
{
    ACE_UNUSED_ARG(i);

    got_sighup = 1;

    OPTIONS->read_config_files();
}

static void print_version()
{
    std::cout << "version " << PACKAGE_VERSION << std::endl;
}

/**
 * Main function.
 * @param argc number of command-line arguments.
 * @param argv array of command-line arguments.
 */
int main(int argc, char** argv)
{
    std::string conffile;

    /*
     * FIXME: The logger is not set up at this point, so ACE_DEBUG
     * prints to stdout.
     */
#if 0
    ACE_DEBUG((LM_DEBUG, "reading config files\n"));
#endif

    OPTIONS->parse(argc, argv, conffile);

    if (!OPTIONS->read_config_files()) {
#if 0
        ACE_DEBUG((LM_ERROR, "error reading config files\n"));
#endif
    }

    int daemon_mode = 0;
    int version = 0;

    static struct poptOption optionsTable[] = {
        { "daemon", 'd', POPT_ARG_NONE, &daemon_mode, 0, "Use daemon mode", NULL },
        { "version", 'v', POPT_ARG_NONE, &version, 0, "Display cryptoserver version", NULL },
        POPT_AUTOHELP
        POPT_TABLEEND
    };

    poptContext optCon = poptGetContext(argv[0], argc, const_cast<const char**>(argv), optionsTable, 0);

    int rc = poptGetNextOpt(optCon);

    if (rc < -1) {
        std::cerr << poptBadOption(optCon, rc) << ": " << poptStrerror(rc) << std::endl;
        return rc;
    }

    poptFreeContext(optCon);

    if (version == 1) {
        print_version();
        return 0;
    }

    if (daemon_mode == 1) {
        OPTIONS->daemon = true;
        OPTIONS->logging = "syslog";
    }

    if (OPTIONS->logging == "syslog") {
        ACE_LOG_MSG->open(PACKAGE_NAME,
                          ACE_Log_Msg::VERBOSE_LITE | ACE_Log_Msg::SYSLOG,
                          ACE_TEXT(PACKAGE_NAME));
        ACE_LOG_MSG->priority_mask(LOG_LEVEL, ACE_Log_Msg::PROCESS);
        ACE_LOG_MSG->priority_mask(LOG_LEVEL, ACE_Log_Msg::THREAD);
    } else if (OPTIONS->logging == "on") {
        ACE_LOG_MSG->open(PACKAGE_NAME,
                          ACE_Log_Msg::VERBOSE_LITE |
                          ACE_Log_Msg::STDERR,
                          ACE_TEXT(PACKAGE_NAME));
        ACE_LOG_MSG->priority_mask(LOG_LEVEL, ACE_Log_Msg::PROCESS);
        ACE_LOG_MSG->priority_mask(LOG_LEVEL, ACE_Log_Msg::THREAD);
    }

    if (OPTIONS->daemon) {
        /* Print startup message. */
        ACE_DEBUG((LM_STARTUP, "starting up server as daemon\n"));

#if HAVE_DAEMON
        if (daemon(1, 1) < 0) {
            ACE_DEBUG((LM_ERROR, "error making daemon\n"));
        }
#else
        ACE_DEBUG((LM_WARNING, "daemon() not supported\n"));
#endif

        std::ofstream pidfile(PID_FILE);

        if (!pidfile) {
            ACE_DEBUG((LM_ERROR, "error creating pid file: %s\n", PID_FILE));
        }

        ACE_DEBUG((LM_INFO, "pid: %d\n", ACE_OS::getpid()));
        ACE_DEBUG((LM_INFO, "pidfile: %s\n", PID_FILE));

        pidfile << ACE_OS::getpid() << std::endl;

        pidfile.close();
    } else {
        ACE_DEBUG((LM_STARTUP, "starting up server not as daemon\n"));
    }

#ifdef ENABLE_SSL
    /* Set certificate and key. */
    ACE_DEBUG((LM_INFO, "SSL enabled\n"));
    ACE_SSL_Context* context = ACE_SSL_Context::instance();
    ACE_DEBUG((LM_INFO, "Using certficate file: %s\n", ACE_DEFAULT_SSL_CERT_DIR"/"ADDERD_CERT));
    context->certificate(ACE_DEFAULT_SSL_CERT_DIR"/"ADDERD_CERT, SSL_FILETYPE_PEM);
    ACE_DEBUG((LM_INFO, "Using private key file: %s\n", ACE_DEFAULT_SSL_CERT_DIR"/"ADDERD_KEY));
    context->private_key(ACE_DEFAULT_SSL_CERT_DIR"/"ADDERD_KEY, SSL_FILETYPE_PEM);

    /* Define SSL-enabled acceptor object to handle network connections. */
    ACE_Acceptor<ClientHandler, ACE_SSL_SOCK_ACCEPTOR> peer_acceptor;
#else
    ACE_DEBUG((LM_INFO, "SSL disabled\n"));
    /* Define acceptor object to handle network connections. */
    ACE_Acceptor<ClientHandler, ACE_SOCK_ACCEPTOR> peer_acceptor;
#endif

    ClientHandler::initialize_function_map();

    /* Try opening the acceptor. If we fail, return an error. */
    if (peer_acceptor.open(ACE_INET_Addr(OPTIONS->port)) == -1) {
        ACE_ERROR_RETURN((LM_ERROR, "%p\n", "open"), -1);
    }

    /* Register the SIGINT signal handler. */
    ACE_Sig_Action sa_sigint((ACE_SignalHandler)sigint_handler, SIGINT);

    /* Register the SIGHUP signal handler. */
    ACE_Sig_Action sa_sighup((ACE_SignalHandler)sighup_handler, SIGHUP);

    ACE_DEBUG((LM_DEBUG, "initializing UUID generator\n"));

    ACE_Utils::UUID_GENERATOR::instance()->init();

    ACE_Reactor::instance()->run_reactor_event_loop();

    /* Print shutdown message. */
    ACE_DEBUG((LM_SHUTDOWN, "shutting down server...\n"));

    return 0;
}
