import sys
import os
import errno
import logging
import const

log = logging.getLogger('')

def root(*dir):
    "convert a data dir to a root relative path"
    return os.path.join(const.root, *dir)

def fatal(msg, *p):
    "log fatal messages and exit"
    if len(p) != 0:
        msg = msg % p
    log.exception(msg)
    log.critical("Cannot continue")
    sys.exit(1)

def writeto(fname, data):
    "save data into fname"
    try:
        with open(fname, "w") as f:
            f.write(str(data))
    except OSError as e:
        log.exception("Could not write to %s" % fname)
        sys.exit(1)

def genwriteto(fname, gen):
    "save data into fname"
    try:
        with open(fname, "w") as f:
            f.writelines(gen)
    except OSError as e:
        log.exception("Could not write to %s" % fname)
        sys.exit(1)

def readfrom(fname, default=None):
    "return contents of fname as string, if we can't read: returns default if not None, otherwise shuts down"
    try:
        with open(fname, "r") as f:
            return f.read()
    except Exception as e:
        if default is not None:
            return default
        log.exception("Could not read from %s" % fname)
        sys.exit(1) 

def mkdirp(*path):
     "Copy of mkdir -p, joins all arguments as path elements"
     if len(path) == 0:
         return
     path = os.path.join(*path)
     try:
         os.makedirs(path)
     except Exception as e:
         if e.errno == errno.EEXIST:
            return # an ignorable error, dir already exists
         log.exception("Could not create directory %s" % path)
         sys.exit(1)

def rmf(*path):
    "Copy of rm -f, joins all arguments as path elements"
    if len(path) == 0:
        return
    path = os.path.join(*path)
    try:
        os.unlink(path)
    except OSError as e:
        if e.errno == errno.ENOENT:
            return
        log.exception("Could not remove file " + path)
        sys.exit(1)

def pairs(list):
    """walk through list returning two elements at a time.
     Assumes len(list) is even."""
    for i in range(0, len(list), 2):
        yield list[i:i+2]

