def ask(prompt, verifier=str, default=None):
    """
    Ask user for a value with simple constraint checking and reprompting on
    error. Supports defaults.

    verifier, if specified, is a callable that either acts as the identity 
    function or raises an exception. If no exception is raised, the value is 
    returned. If there is a valid_range method on the verifier object the output
    of that method is included in the prompt.

    default, if specified, may be either a value or 2 tuple. If it is a 2
    tuple, the first cell is string to use in the prompt and the second is the
    default value to return.

    The default value is NOT run through the verifier.
    """
    valid_range = ""
    try:
        valid_range = " (%s)" % verifier.valid_range()
    except AttributeError:
        pass

    def_str = ""
    default_value = default
    if default is not None:
        if type(default) is tuple:
            def_str, default_value = default
        else:
            def_str = str(default)
        def_str = " [default: %s]" % default_value

    inp = raw_input("%s%s%s: " % (prompt, valid_range, def_str))

    if inp == "":
        if default is None:
            print "No input, try again: ",
            return ask(prompt, verifier, default)
        return default_value
    
    try:
        return verifier(inp)
    except KeyboardInterrupt:
        raise
    except:
        print "Invalid input, try again: ",
        return ask(prompt, verifier, default) 

def _nverifier(typ):
    class i(object):
        def __init__(self, lo, hi):
            self.hi, self.lo = hi, lo
        def __call__(self, v):
            x = typ(v)
            if not (self.lo <= x <= self.hi):
                raise ValueError()
            return x
        def valid_range(self):
            return "%s-%s" % (self.lo, self.hi)
    return i

IntIn = _nverifier(int)
FloatIn = _nverifier(float)

def CSV(typ=str):
    return lambda inp: [typ(x.strip()) for x in inp.split(",")]

def YesNo(inp):
    inp = input.strip().lower()
    if inp in ("yes", "y"):
        return True
    if inp in ("no", "n"):
        return False
    raise ValueError()

class Enum(object):
    def __init__(self, *a):
        self.items = a
    def valid_range(self):
        return ", ".join(self.items)
    def __call__(self, v):
        if v not in self.items:
            raise ValueError(v + " not in " + self.valid_range())
        return v

