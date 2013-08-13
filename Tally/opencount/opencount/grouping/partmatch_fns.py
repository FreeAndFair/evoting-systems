import sys, os

try:
    import cPickle as pickle
except ImportError as e:
    print "Can't import cPickle. Falling back to pickle."
    import pickle

sys.path.append('../')

import pixel_reg.part_match as part_match

"""
A series of helper functions in order to integrate the digit 'reject'
UI step, and the partmatch* function feedback loop.
"""

"""
Output:
<projdir>/rejected_hashes.p
    {str imgpath: {str digit: [((y1,y2,x1,x2), str side_i), ...]}}

<projdir>/accepted_hashes.p
    {str imgpath: {str digit: [((y1,y2,x1,x2), str side_i), ...]}}

"""

def get_rejected_hashes(project):
    """ Returns the rejected_hashes for the entire data set.
    Returns:
        {str imgpath: {str digit: [((y1,y2,x1,x2),side_i,isflip_i), ...]}}
        or None if rejected_hashes.p doesn't exist yet.
    """
    rej_path = os.path.join(project.projdir_path, project.rejected_hashes)
    if not os.path.exists(rej_path):
        return None
    return pickle.load(open(rej_path, 'rb'))
    
def save_rejected_hashes(project, rejected_hashes):
    """ Saves the newer-version of rejected_hashes. """
    rej_path = os.path.join(project.projdir_path, project.rejected_hashes)
    pickle.dump(rejected_hashes, open(rej_path, 'wb'))

def get_accepted_hashes(proj):
    """ Returns the accepted_hashes for the entire data set.
    Returns:
        {str imgpath: {str digit: [((y1,y2,x1,x2),side_i,isflip_i), ...]}}
        or None if accepted_hashes.p doesn't exist yet.
    """
    filepath = os.path.join(proj.projdir_path, proj.accepted_hashes)
    if not os.path.exists(filepath):
        return None
    return pickle.load(open(filepath, 'rb'))

def save_accepted_hashes(proj, accepted_hashes):
    """ Saves the newer-version of accepted_hashes. """
    outpath = os.path.join(proj.projdir_path, proj.accepted_hashes)
    pickle.dump(accepted_hashes, open(outpath, 'wb'))
