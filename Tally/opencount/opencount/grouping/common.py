import sys, os, pdb, time, traceback
from os.path import join as pathjoin

try:
    import cPickle as pickle
except ImportError as e:
    print "Can't import cPickle. Falling back to pickle."
    import pickle

import wx
import numpy as np
import scipy.cluster.vq
from scipy import misc

sys.path.append('../')
sys.path.append('../pixel_reg/')
import pixel_reg.shared as sh
import pixel_reg.part_match as part_match

from specify_voting_targets.imageviewer import WorldState as WorldState
from specify_voting_targets.imageviewer import BoundingBox as BoundingBox
from util import encodepath
import specify_voting_targets.util_gui as util_gui
import cust_attrs
import cluster_imgs
import partask

DUMMY_ROW_ID = -42 # Also defined in label_attributes.py

# Special ID's used for Attributes
TABULATION_ONLY_ID = 1
DIGIT_BASED_ID = 2

class AttributeBox(BoundingBox):
    """
    Represents a bounding box around a ballot attribute.
    """

    def __init__(self, x1, y1, x2, y2, label='', color=None, 
                 id=None, is_contest=False, contest_id=None, 
                 target_id=None,
                 line_width=None, children=None,
                 is_new=False, is_selected=False,
                 attrs=None, side='front', is_digitbased=False,
                 is_tabulationonly=False):
        """
        attrs is a dict mapping:
            {str attrtype: str attrval}
        is_tabulationonly: True if this Attribute is not used for grouping
                           purposes, i.e. is only for tabulation purposes.
        """
        BoundingBox.__init__(self, x1, y1, x2, y2, label=label, color=color,
                             id=id, is_contest=is_contest, contest_id=contest_id,
                             target_id=target_id,
                             line_width=line_width, children=children,
                             is_new=is_new, is_selected=is_selected)
        self.attrs = attrs if attrs else {}
        self.side = side
        self.is_digitbased = is_digitbased
        self.is_tabulationonly = is_tabulationonly

    def has_attrtype(self, attrtype):
        return attrtype in self.attrs

    def get_attrval(self, attrtype):
        return self.attrs.get(attrtype, None)

    def get_attrtypes(self):
        return tuple(self.attrs.keys())

    def add_attrtypes(self, attrtypes, attrvals=None):
        if not attrvals:
            attrvals = (None,)*len(attrtypes)
        assert len(attrtypes) == len(attrvals)
        for i, attrtype in enumerate(attrtypes):
            self.set_attrtype(attrtype, attrvals[i])

    def add_attrtype(self, attrtype, attrval=None):
        self.attrs[attrtype] = attrval

    def set_attrtype(self, attrtype, attrval=None):
        self.attrs[attrtype] = attrval

    def remove_attrtype(self, attrtype):
        assert attrtype in self.attrs, "Error - {0} was not found in \
self.attrs: {1}".format(attrtype, self.attrs)
        self.attrs.pop(attrtype)

    def relabel_attrtype(self, oldname, newname):
        assert oldname in self.attrs, "Error - {0} was not found in \
self.attrs: {1}".format(oldname, self.attrs)
        oldval = self.get_attrval(oldname)
        self.remove_attrtype(oldname)
        self.set_attrtype(newname, oldval)

    def copy(self):
        """ Return a copy of myself """
        return AttributeBox(self.x1, self.y1, 
                           self.x2, self.y2, label=self.label,
                           color=self.color, id=self.id, is_contest=self.is_contest,
                           contest_id=self.contest_id, is_new=self.is_new,
                           is_selected=self.is_selected,
                           target_id=self.target_id,
                            attrs=self.attrs,
                            side=self.side, is_digitbased=self.is_digitbased,
                            is_tabulationonly=self.is_tabulationonly)

    def marshall(self):
        """
        Return a dict-equivalent of myself.
        """
        data = BoundingBox.marshall(self)
        data['attrs'] = self.attrs
        data['side'] = self.side
        data['is_digitbased'] = self.is_digitbased
        data['is_tabulationonly'] = self.is_tabulationonly
        return data

    @staticmethod
    def unmarshall(data):
        box = AttributeBox(0,0,0,0)
        for (propname, propval) in data.iteritems():
            setattr(box, propname, propval)
        return box

    def __eq__(self, a):
        return (a and self.x1 == a.x1 and self.y1 == a.y1 and self.x2 == a.x2
                and self.y2 == a.y2 and self.is_contest == a.is_contest
                and self.label == a.label and self.attrs == a.attrs 
                and self.side == a.side and self.is_digitbased == a.is_digitbased
                and self.is_tabulationonly == a.is_tabulationonly)
    def __repr__(self):
        return "AttributeBox({0},{1},{2},{3},attrs={4},side={5},is_digitbased{6},is_tabonly{7})".format(self.x1, self.y1, self.x2, self.y2, self.attrs, self.side, self.is_digitbased, self.is_tabulationonly)
    def __str___(self):
        return "AttributeBox({0},{1},{2},{3},attrs={4},side={5},is_digitbased{6},is_tabonly{7})".format(self.x1, self.y1, self.x2, self.y2, self.attrs, self.side, self.is_digitbased, self.is_tabulationonly)

class IWorldState(WorldState):
    def __init__(self, box_locations=None):
        WorldState.__init__(self, box_locations=box_locations)

    def get_attrpage(self, attrtype):
        return self.get_attrbox(attrtype).side

    def get_attrtypes(self):
        """
        Return a list of all attribute types.
        """
        result = set()
        for b in self.get_attrboxes():
            for attrtype in b.get_attrtypes():
                result.add(attrtype)
        return list(result)

    def get_attrbox(self, attrtype):
        """
        Return the AttributeBox with given attrtype.
        """
        for b in self.get_boxes_all_list():
            if b.has_attrtype(attrtype):
                return b
        print "== Error: In IWorldState.get_attrbox, no AttributeBox \
with type {0} was found."
        return None

    def get_attrboxes(self):
        """
        Return all AttributeBoxes in a flat list.
        """
        return self.get_boxes_all_list()

    def remove_attrtype(self, attrtype):
        """
        Removes the attrtype from all instances of AttributeBoxes.
        """
        for temppath, boxes in self.box_locations.iteritems():
            for b in boxes:
                if attrtype in b.get_attrtypes():
                    b.remove_attrtype(attrtype)
        self._remove_empties()

    def _remove_empties(self):
        newboxlocs = {}
        for temppath, boxes in self.box_locations.iteritems():
            newboxlocs[temppath] = [b for b in boxes if b.get_attrtypes()]
        self.box_locations = newboxlocs

    def remove_attrbox(self, box):
        for temppath in self.box_locations:
            if box in self.get_boxes(temppath):
                self.remove_box(temppath, box)

    def mutate(self, iworld):
        WorldState.mutate(self, iworld)

def dump_attrboxes(attrboxes, filepath):
    listdata = [b.marshall() for b in attrboxes]
    f = open(filepath, 'wb')
    pickle.dump(listdata, f)
    f.close()
def load_attrboxes(filepath):
    f = open(filepath, 'rb')
    listdata = pickle.load(f)
    f.close()
    return [AttributeBox.unmarshall(b) for b in listdata]



def marshall_iworldstate(world):
    """
    Marshall world.box_locations such that it's 
    possible to pickle them.
    """
    boxlocs = {}
    for temppath, boxes in world.box_locations.iteritems():
        for b in boxes:
            b_data = b.marshall()
            boxlocs.setdefault(temppath, []).append(b_data)
    return boxlocs

def unmarshall_iworldstate(data):
    """
    Unmarshall data, which is of the form:
        <boxlocations data>
    to return a new IWorldState.
    """
    iworld = IWorldState()
    new_boxlocations = {}
    boxlocsdata = data
    for temppath, boxesdata in boxlocsdata:
        for b_data in boxesdata:
            box = AttributeBox.unmarshall(b_data)
            new_boxlocations.setdefault(temppath, []).append(box)
    iworld.box_locations = new_boxlocations
    return iworld

def load_iworldstate(filepath):
    f = open(filepath, 'rb')
    data = pickle.load(filepath)
    return unmarshall_iworldstate(data)

def dump_iworldstate(iworld, filepath):
    f = open(filepath, 'wb')
    pickle.dump(marshall_iworldstate(iworld), f)
    f.close()

def resize_img_norescale(img, size):
    """ Resizes img to be a given size without rescaling - it only
    pads/crops if necessary.
    Input:
        obj img: a numpy array
        tuple size: (w,h)
    Output:
        A numpy array with shape (h,w)
    """
    w,h = size
    shape = (h,w)
    out = np.zeros(shape)
    i = min(img.shape[0], out.shape[0])
    j = min(img.shape[1], out.shape[1])
    out[0:i,0:j] = img[0:i, 0:j]
    return out

def get_attrtypes(project, with_digits=True):
    """
    Returns all attribute types in this election. Excludes CustomAttributes,
    but does include DigitAttributes (if with_digits is True).
    """
    attrtypes = pickle.load(open(project.ballot_attributesfile, 'rb'))
    result = set()
    for attrdict in attrtypes:
        if not attrdict['is_digitbased']:
            attrs_str = get_attrtype_str(attrdict['attrs'])
            result.add(attrs_str)
        elif with_digits and attrdict['is_digitbased']:
            attrs_str = get_attrtype_str(attrdict['attrs'])
            result.add(attrs_str)
    return result

def get_attrtypes_all(project):
    """
    Returns all attrtypes, including CustomAttributes.
    """
    attrtypes = list(get_attrtypes(project))
    cattrs = cust_attrs.load_custom_attrs(project)
    if cattrs != None:
        for cattr in cattrs:
            attrtypes.append(cattr.attrname)
    return set(attrtypes)

def exists_imgattrs(proj):
    """ Returns True if there exists at least one image based attribute
    (i.e. a non-custom+non-digit based attr).
    """
    # attrs does NOT include CustomAttributes (these are stored in 
    # custom_attrs.p), so no need to check for them.
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        if not attr['is_digitbased']:
            return True
    return False

def exists_digitattrs(proj):
    """ Returns True if there exists at least one digit-based attr. """
    attrs = pickle.load(open(proj.ballot_attributesfile, 'rb'))
    for attr in attrs:
        if attr['is_digitbased']:
            return True
    return False

def exists_customattrs(proj):
    """ Returns True if there exists at least one Custom attr. """
    customattrsP = pathjoin(proj.projdir_path, proj.custom_attrs)
    return os.path.exists(customattrsP)

def is_tabulationonly(project, attrtype):
    """ Returns True if the attrtype is for tabulationonly. """
    # 1.) Try imgbased+digitbased attributes
    attrtypes_dicts = pickle.load(open(project.ballot_attributesfile, 'rb'))
    for attrdict in attrtypes_dicts:
        attrs_str = '_'.join(attrdict['attrs'])
        if attrs_str == attrtype:
            return attrdict['is_tabulationonly']
    # 2.) Try custom attributes
    customattrs = cust_attrs.load_custom_attrs(project)
    for cattr in customattrs:
        if cattr.attrname == attrtype:
            return cattr.is_tabulationonly
    # Means we can't find attrtype anywhere.
    assert False, "Can't find attrtype: {0}".format(attrtype)

def is_digitbased(project, attrtype):
    """ Returns True if the attrtype is digit-based. """
    attrtypes_dicts = pickle.load(open(project.ballot_attributesfile, 'rb'))
    for attrdict in attrtypes_dicts:
        attrs_str = '_'.join(attrdict['attrs'])
        if attrs_str == attrtype:
            return attrdict['is_digitbased']
    # 2.) Try custom attributes
    customattrs = cust_attrs.load_custom_attrs(project)
    if customattrs:
        for cattr in customattrs:
            if cattr.attrname == attrtype:
                return False
    # Means we can't find attrtype anywhere.
    assert False, "Can't find attrtype: {0}".format(attrtype)

def is_quarantined(project, path):
    """ Returns True if the image path was quarantined by the user. """
    if not os.path.exists(project.quarantined):
        return False
    f = open(project.quarantined, 'r')
    for line in f:
        if line:
            l = line.strip()
            if os.path.abspath(l) == os.path.abspath(path):
                return True
    f.close()
    return False

def get_attrpair_grouplabel(project, gl_idx, gl_record=None):
    """ Given a grouplabel, return both the attrtype of the grouplabel
    and the attrval. Assumes the newer grouplabel_record interface.
    """
    # Assumes that non-digitbased grouplabels look like:
    #     frozenset([('party', 'democratic'), ('imageorder', 1), ('flip', 0)])
    if type(gl_idx) != int:
        print "Uhoh, expected int index, got {0} instead.".format(type(gl_idx))
        traceback.print_exc()
        pdb.set_trace()

    if gl_record == None:
        gl_record = load_grouplabel_record(project)
    grouplabel = gl_record[gl_idx]
    attrtype, attrval = None, None
    for (k, v) in grouplabel:
        if k != 'imageorder' and k != 'flip':
            attrtype = k
            attrval = v
            break
    return attrtype, attrval

def get_attr_side(project, attrtype):
    """ Returns which side of the ballot this attrtype was defined
    on.
    """
    ballot_attrs = pickle.load(open(project.ballot_attributesfile, 'rb'))
    for attrdict in ballot_attrs:
        attrstr = get_attrtype_str(attrdict['attrs'])
        if attrstr == attrtype:
            return attrdict['side']
    customattrs = cust_attrs.load_custom_attrs(project)
    for cattr in customattrs:
        if cattr.attrname == attrtype:
            # The side is irrelevant.
            return 0
    print "Uhoh, couldn't find attribute:", attrtype
    pdb.set_trace()
    return None

def get_attr_prop(project, attrtype, prop):
    """ Returns the property of the given attrtype. """
    ballot_attrs = pickle.load(open(project.ballot_attributesfile, 'rb'))
    for attrdict in ballot_attrs:
        attrstr = get_attrtype_str(attrdict['attrs'])
        if attrstr == attrtype:
            return attrdict[prop]
    print "Uhoh, couldn't find attribute:", attrtype
    pdb.set_trace()
    return None

def get_numdigits(project, attr):
    """Return the number of digits that this digit-based attribute
    has. If this attr is not a digits attribute (or num_digitsmap
    hasn't been created yet), this returns None.
    """
    if not os.path.exists(pathjoin(project.projdir_path,
                                   project.num_digitsmap)):
        return None
    numdigits_map = pickle.load(open(pathjoin(project.projdir_path,
                                              project.num_digitsmap),
                                     'rb'))
    if attr not in numdigits_map:
        return None
    return int(numdigits_map[attr])

def get_digitbased_attrs(project):
    allattrs = get_attrtypes(project)
    return [attr for attr in allattrs if is_digitbased(project, attr)]

def is_digit_grouplabel(gl_idx, project, gl_record=None):
    """ Return True if this grouplabel is digit-based. """
    if type(gl_idx) != int:
        print "Uhoh, expected int index, got {0} instead.".format(type(gl_idx))
        traceback.print_exc()
        pdb.set_trace()

    if gl_record == None:
        gl_record = load_grouplabel_record(project)
    grouplabel = gl_record[gl_idx]
    attrtype = None
    for (k, v) in grouplabel:
        if k != 'imageorder' and k != 'flip':
            attrtype = k
            break
    return is_digitbased(project, attrtype)

def get_attrtype_str(attrtypes):
    """Returns a 'canonical' string-representation of the attributes
    of a ballot attribute.
    Useful if an AttributeBox has multiple attribute defined within
    it. The 'canonical' representation is:
        each attribute sorted in alphabetical order, separated by
        underscores '_'.
    Input:
        lst attrtypes: List of strings
    """
    return '_'.join(sorted(attrtypes))
    
def remove_common_pathpart(rootdir, path):
    """ Given two paths, a root and a path, return just the part of
    path that starts at root:
    >>> remove_common_pathpart('/media/data1/election', 'election/blanks1/bar.png')
    blanks1/bar.png
    """
    rootdir_abs = os.path.abspath(rootdir)
    path_abs = os.path.abspath(path)
    if not rootdir.endswith('/'):
        rootdir += '/'
    if not path_abs.startswith(rootdir_abs):
        print "Wait, wat? Perhaps invalid arguments to remove_common_pathpart"
        pdb.set_trace()
    return path_abs[:len(rootdir_abs)]

def num_common_prefix(*args):
    """
    For each input list L, return the number of common elements amongst
    all lists (starting from L-R ordering).
    Assumes all input lists are of the same length.
    """
    result = 0
    for idx in range(len(args[0])):
        val = args[0][idx]
        for lst in args[1:]:
            if val != lst[idx]:
                return result
        result += 1
    return result

def is_img_ext(f):
    return os.path.splitext(f.lower())[1].lower() in ('.bmp', '.jpg',
                                                      '.jpeg', '.png',
                                                      '.tif', '.tiff')
def get_imagepaths(dir):
    """ Given a directory, return all imagepaths. """
    results = []
    for dirpath, dirnames, filenames in os.path.walk(dir):
        results.append([pathjoin(dirpath, imname) 
                        for imname in filter(is_img_ext, filenames)])
    return results

def save_grouplabel_record(proj, grouplabel_record):
    outP = pathjoin(proj.projdir_path, proj.grouplabels_record)
    pickle.dump(grouplabel_record, open(outP, 'wb'))
def load_grouplabel_record(proj):
    """ Returns None if the grouplabel_record hasn't been created
    yet.
    """
    path = pathjoin(proj.projdir_path, proj.grouplabels_record)
    if not os.path.exists(path):
        return None
    return pickle.load(open(path, 'rb'))

""" GroupLabel Data Type """

def make_grouplabel(*args):
    """ Given k-v tuples, returns a grouplabel.
    >>> make_grouplabel(('precinct', '380400'), ('side', 0))
    """
    return frozenset(args)

def get_propval(gl_idx, property, proj, gl_record=None):
    """ Returns the value of a property in a grouplabel, or None
    if the property isn't present. 
    TODO: Outdated doctest.
    >>> grouplabel = make_grouplabel(('precinct', '380400'), ('side', 0))
    >>> get_propval(grouplabel, 'precinct')
    380400
    >>> get_propval(grouplabel, 'foo') == None
    True
    """
    if type(gl_idx) != int:
        print "Uhoh, expected int index, got {0} instead.".format(type(gl_idx))
        traceback.print_exc()
        pdb.set_trace()
    if gl_record == None:
        gl_record = load_grouplabel_record(proj)
    for k, v in gl_record[gl_idx]:
        if k == property:
            return v
    return None

def str_grouplabel(gl_idx, proj, gl_record=None):
    """ Returns a string-representation of the grouplabel. """
    if type(gl_idx) != int:
        print "Uhoh, expected int index, got {0} instead.".format(type(gl_idx))
        traceback.print_exc()
        pdb.set_trace()

    if gl_record == None:
        gl_record = load_grouplabel_record(proj)
    grouplabel = gl_record[gl_idx]
    kv_pairs = tuple(grouplabel)
    out = ''
    for (k, v) in sorted(kv_pairs):
        out += '{0}->{1}, '.format(k, v)
    return out

def get_median_img(imgpaths):
    """ Given a list of images, return the image with the median average
    intensity.
    """
    scorelist = [] # [(score_i, imgpath_i), ...]
    for imgpath in imgpaths:
        img = scipy.misc.imread(imgpath, flatten=True)
        score = np.average(img)
        scorelist.append((score, imgpath))
    if not scorelist:
        print "No imgpaths passed in."
        return None
    elif len(scorelist) <= 2:
        return scorelist[0][1]
    return scorelist[int(len(scorelist)/2)][1]

def get_avglightest_img(imgpaths):
    """ Given a list of image paths, return the image with the lightest
    average intensity.
    """
    bestpath, bestscore, idx = None, None, None
    for i,imgpath in enumerate(imgpaths):
        img = scipy.misc.imread(imgpath, flatten=True)
        score = np.average(img)
        if bestpath == None or score > bestscore:
            bestpath = imgpath
            bestscore = score
            idx = i
    return bestpath, bestscore, idx

def get_avgdarkest_img(imgpaths):
    """ Given a list of image paths, return the image with the lightest
    average intensity.
    """
    bestpath, bestscore, idx = None, None, None
    for i,imgpath in enumerate(imgpaths):
        img = scipy.misc.imread(imgpath, flatten=True)
        score = np.average(img)
        if bestpath == None or score < bestscore:
            bestpath = imgpath
            bestscore = score
            idx = i
    return bestpath, bestscore, idx

class GroupClass(object):
    """
    A class that represents a potential group of images.
    """
    # A dict mapping {str label: int count}
    ctrs = {}
    def __init__(self, elements, no_overlays=False, user_data=None):
        """
        TODO: Is it really 'sampleid'? Or what?

        elements: A list of (str sampleid, rankedlist, str imgpatch),
                 where sampleid is the ID for this data point. 
                 rankedlist is a list of grouplabels, which should be
                 sorted by confidence (i.e. the most-likely grouplabel
                 should be at index 0).
                 imgpatch is a path to the image that this element
                 represents.
        user_data: Whatever you want it to be. For 'Digit' attributes,
                   this will be a dict that maps:
                     {str patchpath: float score}
                   This will be used during 'Split', for smarter split
                   behavior. TODO: UNUSED.
        """
        # Converting to Tuples didn't seem to help - if anything, it hurt?
        #self.elements = tuple(elements) if type(elements) != tuple else elements
        self.elements = elements
        #for i in range(len(elements)):  # Why did I do this again?
        #    if not issubclass(type(elements[i][1]), list):
        #        self.elements[i] = list((elements[i][0], list(elements[i][1]), elements[i][2]))
        self.no_overlays=no_overlays
        # self.is_misclassify: Used to mark a GroupClass that the user
        # said was 'Misclassified'
        self.is_misclassify = False
        # orderedAttrVals is a list of grouplabels, whose order is 
        # predetermined by some score-metric. Should not change after it
        # is first set.
        self.orderedAttrVals = ()
        
        # The index of the grouplabel (w.r.t self.orderedAttrVals) that
        # this group ostensibly represents. Is 'finalized' when the user
        # clicks 'Ok' within the VerifyOverlay UI.
        self.index = 0

        # self.user_data can be several things. For "digits" attributes,
        # it's a dict mapping {str patchpath: float score}
        self.user_data = user_data

        self.processElements()
        
        s = str(self.getcurrentgrouplabel())
        if s not in GroupClass.ctrs:
            GroupClass.ctrs[s] = 1
        else:
            GroupClass.ctrs[s] += 1

        # is_manual: A flag used by MODE_YESNO2, indicates this group
        # should be labeled manually.
        self.is_manual = False

    @property
    def label(self):
        s = str(self.getcurrentgrouplabel())
        if s not in GroupClass.ctrs:
            GroupClass.ctrs[s] = 1
        return '{0}-{1}'.format(s,
                                GroupClass.ctrs[s])

    @staticmethod
    def merge(*groups):
        """ Given a bunch of GroupClass objects G, return a new GroupClass
        object that 'merges' all of the elements in G.
        """
        new_elements = [] # a list, ((sampleid_i, rlist_i, patchpath_i), ...)
        # TODO: Merge user_data's, though, it's not being used at the moment.
        label = None
        g_type = None
        for group in groups:
            if g_type == None:
                g_type = type(group)
            elif type(group) != g_type:
                print "Can't merge groups with different types."
                pdb.set_trace()
                return None
            
            if label == None:
                label = group.label
            elif group.label != label:
                print "Can't merge groups with different labels."
                pdb.set_trace()
                return None
            new_elements.extend(group.elements)
        if type(g_type) == GroupClass:
            return GroupClass(new_elements)
        else:
            return DigitGroupClass(new_elements)

    def get_overlays(self):
        """ Returns overlayMin, overlayMax """
        if self.no_overlays:
            return None, None
        print "Generating min/max overlays..."
        _t = time.time()
        overlayMin, overlayMax = do_generate_overlays(self)
        print "...Finished Generating min/max overlays. ({0} s)".format(time.time() - _t)
        return overlayMin, overlayMax

    def __eq__(self, o):
        return (o and issubclass(type(o), GroupClass) and
                self.elements == o.elements)
        
    def __str__(self):
        return "GroupClass({0} elems)".format(len(self.elements))
    def __repr__(self):
        return "GroupClass({0} elems)".format(len(self.elements))

    def getcurrentgrouplabel(self):
        return self.orderedAttrVals[self.index]

    def processElements(self):
        """
        Go through the elements, and compile an ordered list of
        gropulabels for self.orderedAttrVals.
        """
        def sanitycheck_rankedlists(elements):
            """Make sure that the first grouplabel for each rankedlist
            are all the same grouplabel.
            TODO: I think this check isn't valid. This check is valid
                  for elements from GroupClasses computed from Kai's
                  grouping code, but, if it's incorrect, and the user
                  manually changes the labelling, then it's entirely
                  feasible for the user to create a GroupClass where
                  the first grouplabel of each rankedlist is not the
                  same.
            """
            '''
            grouplabel = None
            for (elementid, rankedlist, patchpath) in elements:
                if grouplabel == None:
                    if rankedlist:
                        grouplabel = rankedlist[0]
                        continue
                    else:
                        print 'wat, no rankedlist?!'
                        pdb.set_trace()
                elif rankedlist[0] != grouplabel:
                    print "Error, first element of all rankedlists are \
not equal."
                    pdb.set_trace()
            return True
            '''
            return True
        sanitycheck_rankedlists(self.elements)
        # weightedAttrVals is a dict mapping {[attrval, flipped]: float weight}
        weightedAttrVals = {}
        # self.elements is a list of the form [(imgpath_i, rankedlist_i, patchpath_i), ...]
        # where each rankedlist_i is tuples of the form: (attrval_i, flipped_i, imageorder_i)
        for element in self.elements:
            # element := (imgpath, rankedlist, patchpath)
            """
            Ordered templates
            """
            vote = 1.0
            rankedlist = element[1]
            for group in rankedlist:
                if (group not in weightedAttrVals):
                    weightedAttrVals[group] = vote
                else:
                    weightedAttrVals[group] = weightedAttrVals[group] + vote
                
                vote = vote / 2.0
        self.orderedAttrVals = tuple([group
                                      for (group, weight) in sorted(weightedAttrVals.items(), 
                                                                    key=lambda t: t[1],
                                                                    reverse=True)])

    def split_kmeans(self, K=2):
        """ Uses k-means (k=2) to try to split this group. """
        if len(self.elements) == 2:
            if type(self) == GroupClass:
                return (GroupClass((self.elements[0],),
                                   user_data=self.user_data),
                        GroupClass((self.elements[1],),
                                   user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                return (DigitGroupClass((self.elements[0],),
                                   user_data=self.user_data),
                        DigitGroupClass((self.elements[1],),
                                   user_data=self.user_data))
            else:
                print "Wat?"
                pdb.set_trace()

        # 1.) Gather images
        patchpaths = []
        # patchpath_map used to re-construct 'elements' later on.
        patchpath_map = {} # maps {patchpath: (sampleid, rlist)} 
        for (sampleid, rlist, patchpath) in self.elements:
            patchpaths.append(patchpath)
            patchpath_map[patchpath] = (sampleid, rlist)
        # 2.) Call kmeans clustering
        _t = time.time()
        print "...running k-means."
        clusters = cluster_imgs.cluster_imgs_kmeans(patchpaths, k=K, do_downsize=True, do_align=True)
        print "...Completed running k-means ({0} s).".format(time.time() - _t)
        # 3.) Create GroupClasses
        groups = []
        for clusterid, patchpaths in clusters.iteritems():
            print "For clusterid {0}, there are {1} elements.".format(clusterid, len(patchpaths))
            elements = []
            for patchpath in patchpaths:
                elements.append(patchpath_map[patchpath] + (patchpath,))
            if type(self) == GroupClass:
                groups.append(GroupClass(elements,
                                         user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                groups.append(DigitGroupClass(elements,
                                         user_data=self.user_data))
                
        assert len(groups) == K
        return groups

    def split_pca_kmeans(self, K=2, N=3):
        """ Use PCA to help with the split process.
        Input: Set of image patches A, of size NxM
        0.) Discretize the image patch into K N'xM' equally-sized slices.
        1.) Using the discretized image patches A', run PCA to extract
            the slices S that maximize the variance
        2.) Run k-means (k=2) on the slices S.
        """
        if len(self.elements) <= K:
            groups = []
            for element in self.elements:
                if type(self) == GroupClass:
                    groups.append(GroupClass((element,),
                                             user_data=self.user_data))
                elif type(self) == DigitGroupClass:
                    groups.append(DigitGroupClass((element,),
                                             user_data=self.user_data))
                else:
                    print "Wat?"
                    pdb.set_trace()

            return groups
        # 1.) Gather images
        patchpaths = []
        # patchpath_map used to re-construct 'elements' later on.
        patchpath_map = {} # maps {patchpath: (sampleid, rlist)} 
        for (sampleid, rlist, patchpath) in self.elements:
            patchpaths.append(patchpath)
            patchpath_map[patchpath] = (sampleid, rlist)
        # 2.) Call kmeans clustering
        _t = time.time()
        print "...running PCA+k-means."
        clusters = cluster_imgs.cluster_imgs_pca_kmeans(patchpaths, k=K, do_align=True)
        print "...Completed running PCA+k-means ({0} s).".format(time.time() - _t)
        # 3.) Create GroupClasses
        groups = []
        for clusterid, patchpaths in clusters.iteritems():
            print "For clusterid {0}, there are {1} elements.".format(clusterid, len(patchpaths))
            elements = []
            for patchpath in patchpaths:
                elements.append(patchpath_map[patchpath] + (patchpath,))
            if type(self) == GroupClass:
                groups.append(GroupClass(elements,
                                         user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                groups.append(DigitGroupClass(elements,
                                              user_data=self.user_data))
            else:
                print "Wat?"
                pdb.set_trace()
                
        assert len(groups) == K
        return groups

    def split_rankedlist(self):
        """ Perform a split by using the rankedlist outputted by
        Kai's grouping algorithm.
        """
        groups = []
        new_elements = {}
        all_rankedlists = [t[1] for t in self.elements]

        n = num_common_prefix(*all_rankedlists)

        def naive_split(elements):
            mid = int(round(len(elements) / 2.0))
            group1 = elements[:mid]
            group2 = elements[mid:]
            if type(self) == GroupClass:
                groups.append(GroupClass(group1, user_data=self.user_data))
                groups.append(GroupClass(group2, user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                groups.append(DigitGroupClass(group1, user_data=self.user_data))
                groups.append(DigitGroupClass(group2, user_data=self.user_data))
            else:
                print "Wat?"
                pdb.set_trace()
            return groups
            
        if n == len(all_rankedlists[0]):
            print "rankedlists were same for all voted ballots -- \
doing a naive split instead."
            return naive_split(self.elements)

        if n == 0:
            print "== Wait, n shouldn't be 0 here (in GroupClass.split). \
Changing to n=1, since that makes some sense."
            print "Enter in 'c' for 'continue' to continue execution."
            pdb.set_trace()
            n = 1

        # group by index 'n' into each ballots attrslist (i.e. ranked list)
        for (samplepath, rankedlist, patchpath) in self.elements:
            if len(rankedlist) <= 1:
                print "==== Can't split anymore."
                return [self]
            new_group = rankedlist[n]
            new_elements.setdefault(new_group, []).append((samplepath, rankedlist, patchpath))

        if len(new_elements) == 1:
            # no new groups were made -- just do a naive split
            print "After a 'smart' split, no new groups were made. So, \
just doing a naive split."
            return naive_split(self.elements)

        print 'number of new groups after split:', len(new_elements)
        for grouplabel, elements in new_elements.iteritems():
            if type(self) == GroupClass:
                groups.append(GroupClass(elements, user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                groups.append(DigitGroupClass(elements, user_data=self.user_data))
            else:
                print "Wat?"
                pdb.set_trace()
        return groups

    def split_kmeans2(self, K=2):
        """ Performs our hand-rolled K-Means implementation. """
        if len(self.elements) == 2:
            if type(self) == GroupClass:
                return (GroupClass((self.elements[0],),
                                   user_data=self.user_data),
                        GroupClass((self.elements[1],),
                                   user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                return (DigitGroupClass((self.elements[0],),
                                   user_data=self.user_data),
                        DigitGroupClass((self.elements[1],),
                                   user_data=self.user_data))
            else:
                print "Wat?"
                pdb.set_trace()

        # 1.) Gather images
        patchpaths = []
        # patchpath_map used to re-construct 'elements' later on.
        patchpath_map = {} # maps {patchpath: (sampleid, rlist)} 
        for (sampleid, rlist, patchpath) in self.elements:
            patchpaths.append(patchpath)
            patchpath_map[patchpath] = (sampleid, rlist)
        # 2.) Call kmeans clustering
        _t = time.time()
        print "...running k-means2"
        clusters = cluster_imgs.kmeans_2D(patchpaths, k=K, 
                                          distfn_method='vardiff',
                                          do_align=True)
        print "...Completed running k-means2 ({0} s).".format(time.time() - _t)
        # 3.) Create GroupClasses
        groups = []
        found_patchpaths = set()
        for clusterid, c_patchpaths in clusters.iteritems():
            print "For clusterid {0}, there are {1} elements.".format(clusterid, len(c_patchpaths))
            elements = []
            for c_patchpath in c_patchpaths:
                if c_patchpath in found_patchpaths:
                    print "Uhoh, element {0} was present in multiple clusters.".format(c_patchpath)
                    pdb.set_trace()
                found_patchpaths.add(c_patchpath)
                elements.append(patchpath_map[c_patchpath] + (c_patchpath,))
            if type(self) == GroupClass:
                groups.append(GroupClass(elements,
                                         user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                groups.append(DigitGroupClass(elements,
                                         user_data=self.user_data))
        if len(found_patchpaths) != len(patchpaths):
            print "Uhoh, only found {0} patchpaths, but should have found {1}".format(len(found_patchpaths),
                                                                                      len(patchpaths))
            pdb.set_trace()
        assert len(groups) == K
        return groups

    def split_kmediods(self, K=2):
        """ Performs our hand-rolled K-Mediods implementation. """
        if len(self.elements) == 2:
            if type(self) == GroupClass:
                return (GroupClass((self.elements[0],),
                                   user_data=self.user_data),
                        GroupClass((self.elements[1],),
                                   user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                return (DigitGroupClass((self.elements[0],),
                                   user_data=self.user_data),
                        DigitGroupClass((self.elements[1],),
                                   user_data=self.user_data))
            else:
                print "Wat?"
                pdb.set_trace()

        # 1.) Gather images
        patchpaths = []
        # patchpath_map used to re-construct 'elements' later on.
        patchpath_map = {} # maps {patchpath: (sampleid, rlist)} 
        for (sampleid, rlist, patchpath) in self.elements:
            patchpaths.append(patchpath)
            patchpath_map[patchpath] = (sampleid, rlist)
        # 2.) Call kmeans clustering
        _t = time.time()
        print "...running k-mediods."
        clusters = cluster_imgs.kmediods_2D(patchpaths, k=K, 
                                            distfn_method='vardiff',
                                            do_align=True)
        print "...Completed running k-mediods ({0} s).".format(time.time() - _t)
        # 3.) Create GroupClasses
        groups = []
        for clusterid, patchpaths in clusters.iteritems():
            print "For clusterid {0}, there are {1} elements.".format(clusterid, len(patchpaths))
            elements = []
            for patchpath in patchpaths:
                elements.append(patchpath_map[patchpath] + (patchpath,))
            if type(self) == GroupClass:
                groups.append(GroupClass(elements,
                                         user_data=self.user_data))
            elif type(self) == DigitGroupClass:
                groups.append(DigitGroupClass(elements,
                                         user_data=self.user_data))
                
        assert len(groups) == K
        return groups
        
    def split(self, mode='kmeans'):
        if mode == 'rankedlist':
            return self.split_rankedlist()
        elif mode == 'kmeans':
            return self.split_kmeans(K=2)
        elif mode == 'pca_kmeans':
            return self.split_pca_kmeans(K=3)
        elif mode == 'kmeans2':
            return self.split_kmeans2(K=2)
        elif mode == 'kmediods':
            return self.split_kmediods(K=2)
        else:
            print "Unrecognized mode: {0}. Defaulting to kmeans.".format(mode)
            return self.split_kmeans(K=2)

class DigitGroupClass(GroupClass):
    """
    A class that represents a potential group of digits.
    """
    def __init__(self, elements, no_overlays=False, user_data=None,
                 *args, **kwargs):
        GroupClass.__init__(self, elements, no_overlays=no_overlays,
                            user_data=user_data)

    def split_medianwise(self):
        """
        TODO: NOT IN USE. Replaced by split_kmeans(), since it seems to
              work better.
        """
        # Assumes that only Digit attributes is using self.user_data.
        # Split the elements based on the partmatch scores: the top
        # 50%, and the bottom 50%.
        # self.user_data: {str patchpath: float score}
        # 0.) Check degenerate case
        if len(self.elements) == 2:
            return (DigitGroupClass((self.elements[0],),
                                    user_data=self.user_data),
                    DigitGroupClass((self.elements[1],),
                                    user_data=self.user_data))
        # 1.) Compute median score
        scores = []
        for (sampleid, rlist, patchpath) in self.elements:
            if patchpath not in self.user_data:
                print "Uhoh, patchpath not in self.user_data."
                pdb.set_trace()
            score = self.user_data[patchpath]
            scores.append(score)
        scores = sorted(scores)
        median = scores[int(len(scores) / 2)]
        print "MEDIAN WAS:", median
        # 2.) Group high and low scores
        elements1, elements2 = [], []
        for (sampleid, rlist, patchpath) in self.elements:
            score = self.user_data[patchpath]
            if score > median:
                elements1.append((sampleid, rlist, patchpath))
            else:
                elements2.append((sampleid, rlist, patchpath))
        return (DigitGroupClass(elements1, user_data=self.user_data),
                DigitGroupClass(elements2, user_data=self.user_data))

    def split_kmeans(self, K=2):
        """ Uses k-means (k=2) to try to split this group. """
        if len(self.elements) == 2:
            return (DigitGroupClass((self.elements[0],),
                                    user_data=self.user_data),
                    DigitGroupClass((self.elements[1],),
                                    user_data=self.user_data))
        # 1.) Gather images
        patchpaths = []
        # patchpath_map used to re-construct 'elements' later on.
        patchpath_map = {} # maps {patchpath: (sampleid, rlist)} 
        for (sampleid, rlist, patchpath) in self.elements:
            patchpaths.append(patchpath)
            patchpath_map[patchpath] = (sampleid, rlist)
        # 2.) Call kmeans clustering
        _t = time.time()
        print "...running k-means."
        clusters = cluster_imgs.cluster_imgs_kmeans(patchpaths, k=K, do_align=True)
        print "...Completed running k-means ({0} s).".format(time.time() - _t)
        # 3.) Create DigitGroupClasses
        groups = []
        for clusterid, patchpaths in clusters.iteritems():
            print "For clusterid {0}, there are {1} elements.".format(clusterid, len(patchpaths))
            elements = []
            for patchpath in patchpaths:
                elements.append(patchpath_map[patchpath] + (patchpath,))
            groups.append(DigitGroupClass(elements,
                                          user_data=self.user_data))
        assert len(groups) == K
        return groups
        

def do_generate_overlays(group):
    """ Given a GroupClass, generate the Min/Max overlays. """
    if len(group.elements) <= 20:
        # Just do it all in serial.
        return _generate_overlays(group.elements)
    else:
        return partask.do_partask(_generate_overlays,
                                  group.elements,
                                  combfn=_my_combfn_overlays,
                                  init=(None, None))

def _generate_overlays(elements):
    overlayMin, overlayMax = None, None
    for element in elements:
        path = element[2]
        img = misc.imread(path, flatten=1)
        if (overlayMin == None):
            overlayMin = img
        else:
            if overlayMin.shape != img.shape:
                h, w = overlayMin.shape
                img = resize_img_norescale(img, (w,h))
            overlayMin = np.fmin(overlayMin, img)
        if (overlayMax == None):
            overlayMax = img
        else:
            if overlayMax.shape != img.shape:
                h, w = overlayMax.shape
                img = resize_img_norescale(img, (w,h))
            overlayMax = np.fmax(overlayMax, img)

    rszFac=sh.resizeOrNot(overlayMax.shape,sh.MAX_PRECINCT_PATCH_DISPLAY)
    overlayMax = sh.fastResize(overlayMax, rszFac) #/ 255.0
    overlayMin = sh.fastResize(overlayMin, rszFac) #/ 255.0
    return overlayMin, overlayMax
def _my_combfn_overlays(result, subresult):
    """ result, subresult are (np img_min, np img_max). Overlay the
    min's and max's together.
    """
    imgmin, imgmax = result
    imgmin_sub, imgmax_sub = subresult
    if imgmin == None:
        imgmin = imgmin_sub
    else:
        if imgmin.shape != imgmin_sub.shape:
            h, w = imgmin.shape
            imgmin_sub = resize_img_norescale(imgmin_sub, (w,h))
        imgmin = np.fmin(imgmin, imgmin_sub)
    if imgmax == None:
        imgmax = imgmax_sub
    else:
        if imgmax.shape != imgmax_sub.shape:
            h, w = imgmax.shape
            imgmax_sub = resize_img_norescale(imgmax_sub, (w,h))
        imgmax = np.fmax(imgmax, imgmax_sub)
    return imgmin, imgmax

class TextInputDialog(wx.Dialog):
    """
    A dialog to accept N user inputs.
    """
    def __init__(self, parent, caption="Please enter your input(s).", 
                 labels=('Input 1:',), 
                 vals=('',),
                 *args, **kwargs):
        """
        labels: A list of strings. The number of strings determines the
              number of inputs desired.
        vals: An optional list of values to pre-populate the inputs.
        """
        wx.Dialog.__init__(self, parent, title='Input required', *args, **kwargs)
        self.parent = parent

        # self.results maps {str label: str value}
        self.results = {}

        self.input_pairs = []
        for idx, label in enumerate(labels):
            txt = wx.StaticText(self, label=label)
            input_ctrl = wx.TextCtrl(self, style=wx.TE_PROCESS_ENTER)
            if idx == len(labels) - 1:
                input_ctrl.Bind(wx.EVT_TEXT_ENTER, self.onButton_ok)
            try:
                input_ctrl.SetValue(vals[idx])
            except:
                pass
            self.input_pairs.append((txt, input_ctrl))
        panel_btn = wx.Panel(self)
        btn_ok = wx.Button(panel_btn, id=wx.ID_OK)
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(panel_btn, id=wx.ID_CANCEL)
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        panel_btn.sizer = wx.BoxSizer(wx.HORIZONTAL)
        panel_btn.sizer.Add(btn_ok, border=10, flag=wx.RIGHT)
        panel_btn.sizer.Add(btn_cancel, border=10, flag=wx.LEFT)
        panel_btn.SetSizer(panel_btn.sizer)

        self.sizer = wx.BoxSizer(wx.VERTICAL)
        caption_txt = wx.StaticText(self, label=caption)
        self.sizer.Add(caption_txt, border=10, flag=wx.ALL)
        gridsizer = wx.GridSizer(rows=0, cols=2, hgap=5, vgap=3)
        gridsizer.Add(self.input_pairs[0][0])
        gridsizer.Add(self.input_pairs[0][1])
        for txt, input_ctrl in self.input_pairs[1:]:
            gridsizer.Add(txt, border=10, flag=wx.ALL)
            gridsizer.Add(input_ctrl, border=10, flag=wx.ALL)
        self.gridsizer = gridsizer
        self.sizer.Add(gridsizer)
        self.sizer.Add(panel_btn, border=10, flag=wx.ALL | wx.ALIGN_CENTER)
        self.SetSizer(self.sizer)

        self.Fit()

        self.input_pairs[0][1].SetFocus()

    def onButton_ok(self, evt):
        for txt, input_ctrl in self.input_pairs:
            self.results[txt.GetLabel()] = input_ctrl.GetValue()
        self.EndModal(wx.ID_OK)
    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)

class SingleChoiceDialog(wx.Dialog):
    """
    A Dialog to allow the user to select one of N choices.
    """
    def __init__(self, parent, message="Please make a choice.", choices=[], *args, **kwargs):
        wx.Dialog.__init__(self, parent, *args, **kwargs)
        
        # self.result will be the user-selected choice
        self.result = None

        sizer = wx.BoxSizer(wx.VERTICAL)
        txt1 = wx.StaticText(self, label=message)
        sizer.Add(txt1)
        radio_btns = [] # List of [(str choice_i, obj RadioButton_i), ...]
        self.radio_btns = radio_btns
        for i, choice in enumerate(choices):
            if i == 0:
                radiobtn = wx.RadioButton(self, label=choice, style=wx.RB_GROUP)
            else:
                radiobtn = wx.RadioButton(self, label=choice)
            radio_btns.append((choice, radiobtn))
            sizer.Add(radiobtn)
        btn_sizer = wx.BoxSizer(wx.HORIZONTAL)
        btn_ok = wx.Button(self, label="Ok")
        btn_ok.Bind(wx.EVT_BUTTON, self.onButton_ok)
        btn_cancel = wx.Button(self, label="Cancel")
        btn_cancel.Bind(wx.EVT_BUTTON, self.onButton_cancel)
        btn_sizer.AddMany([(btn_ok,), (btn_cancel,)])
        sizer.Add(btn_sizer, flag=wx.ALIGN_CENTER)
        self.SetSizer(sizer)
        self.Fit()

    def onButton_ok(self, evt):
        for choice, radiobtn in self.radio_btns:
            if radiobtn.GetValue() == True:
                self.result = choice
        self.EndModal(wx.ID_OK)
    def onButton_cancel(self, evt):
        self.EndModal(wx.ID_CANCEL)

def do_digitocr(imgpaths, digit_exs, num_digits, bb=None,
                rejected_hashes=None, accepted_hashes=None,
                digitdist=20):
    """ Basically does what sh.digitParse does, but checks to see if
    the image might be flipped, and if it is, to flip it and return
    the match with the best response.
    Input:
        list imgpaths: list of image paths to perform digit ocr over
        dict digit_exs: maps {str digit: ((str temppath_i, bb_i, exemplarP_i), ...)}
        tuple bb: If given, this is a tuple (y1,y2,x1,x2), which 
                  restricts the ocr search to the given bb.
        dict rejected_hashes: maps {imgpath: {str digit: [((y1,y2,x1,x2),side_i,isflip_i), ...]}}
        dict accepted_hashes: maps {imgpath: {str digit: [((y1,y2,x1,x2),side_i,isflip_i), ...]}}
        int digitdist: The expected distance between adjacent digits.
    Output:
        list of [(imgpath_i, ocrstr_i, meta_i, bool isflip_i), ...]
    """
    def get_best_flip(results_noflip, results_flip):
        """ Given the results of digitParse (both not flipped and
        flipped), return a new results list that, for each voted ballot,
        chooses the match (either flipped/not-flipped) with the highest
        score.
        Input:
            lst results_noflip: list of [(imgpath_i, ocrstr_i, meta_i), ...]
            lst results_flip: list of [(imgpath_i, ocrstr_i, meta_i), ...]
        Output:
            lst results: list of [(imgpath_i, ocrstr_i, meta_i, isflip_i), ...]
        """
        assert len(results_noflip) == len(results_flip)
        results_noflip = sorted(results_noflip, key=lambda tup: tup[0])
        results_flip = sorted(results_flip, key=lambda tup: tup[0])
        results = []
        for idx, (path_noflip, ocrstr_noflip, meta_noflip) in enumerate(results_noflip):
            path_flip, ocrstr_flip, meta_flip = results_flip[idx]
            assert path_noflip == path_flip
            assert len(meta_noflip) == len(meta_flip)
            avg_score_noflip = sum([tup[6] for tup in meta_noflip]) / float(len(meta_noflip))
            avg_score_flip = sum([tup[6] for tup in meta_flip]) / float(len(meta_flip))
            if avg_score_noflip > avg_score_flip:
                results.append((path_noflip, ocrstr_noflip, meta_noflip, False))
            else:
                results.append((path_flip, ocrstr_flip, meta_flip, True))
        assert len(results) == len(results_noflip)
        assert len(results) == len(results_flip)
        return results
    
    if not bb:
        imgsize = misc.imread(imgpath, flatten=True).shape
        bb = (0, imgsize[0], 0, imgsize[1])
    print "======== HSPACE IS:", digitdist
    results_noflip = part_match.digitParse(digit_exs, imgpaths, bb,
                                           num_digits, do_flip=False,
                                           rejected_hashes=rejected_hashes,
                                           accepted_hashes=accepted_hashes,
                                           hspace=digitdist)
    results_flip = part_match.digitParse(digit_exs, imgpaths, bb,
                                         num_digits, do_flip=True,
                                         rejected_hashes=rejected_hashes,
                                         accepted_hashes=accepted_hashes,
                                         hspace=digitdist)
    results_noflip = munge_pm_results(results_noflip)
    results_flip = munge_pm_results(results_flip)
    results_best = get_best_flip(results_noflip, results_flip)
    return results_best

def munge_pm_results(results):
    """ Converts results format from part_match.digitParse to the output
    format of shared.digitParse.
    Input:
        lst results: List of [(imgpath_i, ocrstr_i, imgpatches_i, patchcoords_i, scores_i), ...]
    Output:
        lst of [(imgpath_i, ocrstr_i, meta_i), ...], where each meta_i
        is a list of the form:
            meta_i := (y1,y2,x1,x2,str digit, obj digitimg, float score)
    """
    out = []
    for (imgpath, ocrstr, imgpatches, patchcoords, scores) in results:
        meta = []
        if not (len(imgpatches) == len(patchcoords) == len(scores)):
            print "Uhoh, not all were equal length."
            pdb.set_trace()
        assert len(imgpatches) == len(patchcoords) == len(scores)
        for i, (y1,y2,x1,x2) in enumerate(patchcoords):
            try:
                digit = ocrstr[i]
            except Exception as e:
                print e
                print "OH DEAR. Did you accidently not type in the digit \
during LabelDigitAttrs?"
                pdb.set_trace()
            digitimg = imgpatches[i]
            score = scores[i]
            meta.append((y1,y2,x1,x2,digit,digitimg,score))
        out.append((imgpath, ocrstr, meta))
    return out

def par_extract_patches(tasks):
    """ Parallelizes the following task:
    For N images, extract a boundingbox from each image, and store it
    to disk.
    Input:
        list tasks: ((imgpath_i, bb_i, outpath_i), ...)
    """
    # TODO: I should probably be nuked.
    partask.do_partask(imgmap)
                       
def is_blankballot_contests_eq(*blankpaths):
    """ Returns True if the input blank ballots contain the same contests,
    False otherwise.
    Input:
        list blankpaths: (blankpath_i, ...)
    Output:
        True or False.
    """
    '''
    for i, b1 in enumerate(blankpaths):
        if i == len(blankpaths-1):
            break
        b2 = blankpaths[i+1]
    '''
    # TODO: Implement me!
    return False

if __name__ == '__main__':
    class MyFrame(wx.Frame):
        def __init__(self, parent, *args, **kwargs):
            wx.Frame.__init__(self, parent, *args, **kwargs)
            btn = wx.Button(self, label="Click me")
            btn.Bind(wx.EVT_BUTTON, self.onButton)
            
        def onButton(self, evt):
            dlg = TextInputDialog(self, labels=("Input 1:", "Input 2:", "Input 3:"))
            dlg.ShowModal()
            print dlg.results
    app = wx.App(False)
    frame = MyFrame(None)
    frame.Show()
    app.MainLoop()

def log_misclassify_ballots(proj, elements):
    """ Logs misclassified ballots to a logfile. """
    try:
        logfile = open(os.path.join(proj.projdir_path, 'misclassify.log'), 'a')
        for sampleid, rlist, patchpath in elements:
            print >>logfile, sampleid
    except Exception as e:
        print e
