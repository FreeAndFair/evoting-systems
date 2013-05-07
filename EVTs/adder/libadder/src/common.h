#ifndef COMMON_H
#define COMMON_H

#ifdef LIBADDER_EXPORTS
#define LIBADDER_API __declspec(dllexport)
#else
#define LIBADDER_API
#endif

#include <fstream>

#include "assert.h"
#include "gmp.h"

#endif /* COMMON_H */
