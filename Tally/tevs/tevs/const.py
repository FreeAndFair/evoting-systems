class _const:
    __name__ = __name__

    class ConstError(TypeError): pass

    def __setattr__(self,name,value):
        if self.__dict__.has_key(name):
            raise self.ConstError, "Can't rebind const(%s)" % name
        self.__dict__[name] = value

    def __delattr__(self,name):
        if self.__dict__.has_key(name):
            raise self.ConstError, "Can't unbind const(%s)" % name
        raise NameError, name

import sys
if __name__ not in sys.modules:
    sys.modules[__name__] = _const()

