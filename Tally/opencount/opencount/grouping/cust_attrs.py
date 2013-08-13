import sys, os, pickle
from os.path import join as pathjoin
sys.path.append('..')

"""
Functions that handle the Custom Attributes extension. 

For SpreadSheet-based CustomAttributes, OpenCount assumes that the input
spreadsheetpaths are .csv-like files of the form:

in, out
in_0, out_0
in_1, out_1
...
in_N, out_N

"""

"""
Output files:

<projdir>/custom_attrs.p
  
A list of marshall'd custom_attributes (i.e. dictionaries):
  [m_custattr_i, ... ]
"""

TYPE_CATTR = 'cattr'
TYPE_SPREADSHEET = 'spreadsheet'
TYPE_FILENAME = 'filename'

class CustomAttribute(object):
    def __init__(self, attrname,
                 is_tabulationonly=False):
        """
        str attrname:
        bool is_tabulationonly: 
        """
        self.attrname = attrname
        self.is_tabulationonly = is_tabulationonly
    def marshall(self):
        return {'attrname': self.attrname, 'is_tabulationonly': self.is_tabulationonly,
                'type': TYPE_CATTR}

class Spreadsheet_Attr(CustomAttribute):
    def __init__(self, attrname, sspath, attrin, is_tabulationonly):
        CustomAttribute.__init__(self, attrname, is_tabulationonly)
        self.sspath = sspath
        self.attrin = attrin
    def marshall(self):
        dct = CustomAttribute.marshall(self)
        dct['sspath'] = self.sspath
        dct['attrin'] = self.attrin
        dct['type'] = TYPE_SPREADSHEET
        return dct
        
class Filename_Attr(CustomAttribute):
    def __init__(self, attrname, filename_regex, is_tabulationonly):
        CustomAttribute.__init__(self, attrname, is_tabulationonly)
        self.filename_regex = filename_regex
    def marshall(self):
        dct = CustomAttribute.marshall(self)
        dct['filename_regex'] = self.filename_regex
        dct['type'] = TYPE_FILENAME
        return dct

def dump_custom_attrs(proj, custattrs=None):
    """ Stores the custom_attributes into the correct output location. """
    if custattrs == None:
        custattrs = load_custom_attrs(proj)
    if custattrs == None:
        custattrs = []
    marshalled = [marshall_cust_attr(cattr) for cattr in custattrs]
    pickle.dump(marshalled, open(pathjoin(proj.projdir_path, proj.custom_attrs), 'wb'))

def load_custom_attrs(proj):
    """ Returns the custom_attrs data structure if it exists, or None
    if it doesn't exist yet.
    Input:
      obj project
    Output:
      list of CustomAttribute instances
    """
    path = pathjoin(proj.projdir_path, proj.custom_attrs)
    if not os.path.exists(path):
        return None
    marshalled = pickle.load(open(path, 'rb'))
    return [unmarshall_cust_attr(m) for m in marshalled]

def custattr_get(custom_attrs, attrname):
    """ Returns the CustomAttribute if it exists in custom_attrs,
    or None otherwise.
    """
    if custom_attrs == None:
        return None
    for cattr in custom_attrs:
        if cattr.attrname == attrname:
            return cattr
    return None

def custattr_exists(proj, attrname):
    """ Returns True if attrname is a custom_attribute. """
    custom_attrs = load_custom_attrs(proj)
    if custom_attrs != None:
        return custattr_get(custom_attrs, attrname) != None
    return False
