"Open the zlib compressed template and extract Post-script data"
import zlib, os, sys
mydir = os.path.dirname(sys.modules[__name__].__file__)
ps = os.path.join(mydir, "ps", "postscript.zlib")
BALLOTPS = zlib.decompress(open(ps,"rb").read()).replace("\r\n","\n")
