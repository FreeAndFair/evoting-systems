import sys, pickle
sys.path.append('..')
sys.path.append('../..')
import doGrouping

errdict = '_errdict_0'

"""
A seemingly non-deterministic error:

   python demo.py

The _errdict_<i> files are snapshots of the inputs to
dist2patches, from within doGrouping.templateSSWorker,
around line 222:
    (scores,locs)=dist2patches(patchTuples,sc1)

If you keep running demo.py, on my machine, the error only
sometimes comes up. (like a 50% chance)...

"""

def main():
    d = pickle.load(open(errdict, 'rb'))

    patchTuples = d['patchTuples']
    sc1 = d['sc1']
    
    scores, locs = doGrouping.dist2patches(patchTuples, sc1)
    
if __name__ == '__main__':
    main()
