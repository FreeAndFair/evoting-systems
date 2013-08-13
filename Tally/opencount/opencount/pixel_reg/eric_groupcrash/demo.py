import sys, pickle
import scipy, scipy.misc
sys.path.append('..')
import imagesAlign

errdict = 'err_dict_0'

"""
Calling this will cause a crash, within imagesAlign1:

     python demo.py

I1, Iref1, and type were inputs from my OC-recall races test set
that caused a crash.
"""

def main():
    d = pickle.load(open(errdict, 'rb'))
    I1 = d['I1']
    Iref1 = d['Iref1']
    type = d['type']

    scipy.misc.imsave("I1.png", I1)
    scipy.misc.imsave("Iref1.png", Iref1)

    output = imagesAlign.imagesAlign(I1, Iref1, type=type)
    #H, err = imagesAlign(I1, Iref1, type=type)
    
if __name__ == '__main__':
    main()
