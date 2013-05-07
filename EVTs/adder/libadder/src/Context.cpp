/* -*- Mode: C++; tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*- */

/*  libadder - Cryptographic library for the Adder project.
    Copyright (C) 2004  The Adder Team <adder@cse.uconn.edu>

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
 * @file Context.cpp
 * Implementation of the Context class.
 */

#include <iostream>

#ifdef WIN32
#include "windows.h"
#include "wincrypt.h"
#include "config-win32.h"
#else
#include "sys/types.h"
#include "sys/stat.h"
#include "fcntl.h"
#include "errno.h"
#include "unistd.h"
#include "ctype.h"
#include "config.h"
#endif

#include "common.h"
#include "Context.h"

namespace adder {
    Context::Context(bool secure)
    {
        set_seed(secure);
        init_state();
    }

    Context::~Context()
    {
        gmp_randclear(state);
    }

    gmp_randstate_t* Context::get_state()
    {
        return &state;
    }

    void Context::init_state()
    {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, seed);
    }

    /**
     * This sets the seed to be a combination of the current time and
     * the process ID, a la SSLv2.  Use at your own risk.
     */
    void Context::set_seed_insecure()
    {
#ifdef WIN32
        LARGE_INTEGER lpPerformanceCount;

        QueryPerformanceFrequency(&lpPerformanceCount);

        srand((unsigned int)lpPerformanceCount.QuadPart + GetCurrentProcessId());
#else
        srand((unsigned int)time(0) + getpid());
#endif

        seed = rand();
    }

    void Context::set_seed(bool secure)
    {
        seed = 0;

        if (!secure) {
            set_seed_insecure();
        } else {
#if (WINVER >= 0x0500)
            HCRYPTPROV hCryptProv;
            BOOL bError = FALSE;

            if (!CryptAcquireContext(&hCryptProv, NULL, NULL, PROV_INTEL_SEC, CRYPT_VERIFYCONTEXT | CRYPT_SILENT)) {
                if (!CryptAcquireContext(&hCryptProv, NULL, NULL, PROV_RSA_FULL, CRYPT_VERIFYCONTEXT | CRYPT_SILENT)) {
                    bError = TRUE;
                }
            }

            if (!bError) {
               if (CryptGenRandom(hCryptProv, sizeof(unsigned int), (LPBYTE)&seed)) {
                   if (!CryptReleaseContext(hCryptProv, 0)) {
                       bError = TRUE;
                   }
               } else {
                   bError = TRUE;
               }
            }

            if (bError) {
                throw "error getting seed";
            }
#elif defined(HAVE_ENTROPY_DEVICE)
            int fd;
            int nbytes;
            int i;

            /*
             * Open the file as non-blocking. Some devices like /dev/random will
             * block if there isn't enough entropy available.
             */
            fd = open(ENTROPY_SOURCE, O_RDONLY | O_NONBLOCK | O_NOCTTY);

            if (fd < 0) {
                throw "Cannot open entropy source: " ENTROPY_SOURCE;
            }
    
            nbytes = sizeof(unsigned int);

            while (nbytes > 0) {
                i = read(fd, &seed, nbytes);

                if (i < 0) {
                    /*
                     * If /dev/random does not have enough entropy
                     * available it will set errno to EAGAIN and we
                     * can just try to read it again.
                     */
                    if (errno == EINTR || errno == EAGAIN) {
                        continue;
                    } else {
                        throw "Cannot read from entropy source: " ENTROPY_SOURCE;
                    }
                }

                nbytes -= i;
            }
                
            close(fd);
#else
            throw "Entropy device not supported";
#endif
        }
    }
}
