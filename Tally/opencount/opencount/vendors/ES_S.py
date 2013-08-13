import os
import sys
import traceback
import cv
import barcode.es_s as es_s
from Vendor import Vendor
from os.path import join as pathjoin
from grouping import partask

try:
    import cPickle as pickle
except:
    import pickle

sys.path.append('..')

# Get this script's directory. Necessary to know this information
# since the current working directory may not be the same as where
# this script lives (which is important for loading resources like
# imgs)
try:
    MYDIR = os.path.abspath(os.path.dirname(__file__))
except NameError:
    # This script is being run directly
    MYDIR = os.path.abspath(sys.path[0])

MARK = pathjoin(MYDIR, 'ess_mark.png')
bits = 36

class ESSVendor(Vendor):
    def __init__(self, proj):
        self.proj = proj

    def decode_ballots(self, ballots, manager=None, queue=None, skipVerify=True, *args, **kwargs):
        """
        Decode ES&S style ballot barcodes. 
        Each mark will later be verified for correctness.
        Input:
            ballots : {int ballotID: [imgpath_side0, ...]}.
            manager : option for multiprocessing
            queue   : option for multiprocessing
            skipVerify : If True, then don't store metadata about each
                         individual barcode mark. Simply output an empty
                         dict for the bbs_map output.
        Output:
            img2decoding : stores decoded strings for each image.
            flip_map     : stores whether an image is flipped or not:
                           {str imgpath: bool isFlipped}
            bbs_map      : location of barcode patches (bits) to be verified:
                           {str bc_val: [(str imgpath, (x1,y1,x2,y2), ), ...]}
            err_imgpaths : list of unsuccessfully decoded imgpaths that
                           will be handled specially
            ioerr_imgpaths : list of imgpaths that were unable to be read
                             by OpenCV.
        """
        mark_path = MARK
        # decoded_results: {ballotID: (barcode, is_flipped, bit_locations)}
        decoded_results = decode_ballots(ballots, mark_path, manager, queue)
        img2decoding = {} # {imgpath: (str decoding_0, ..., str decoding_N)}
        flip_map = {}  # {imgpath: is_flipped}
        bbs_map = {}   # {bit_value: [(imgpath, (x1,y1,x2,y2), None), ...]}
        err_imgpaths = []
        ioerr_imgpaths = [] # TODO: Populate me if IOErrors occur!
        counter = 0
        for ballotid, decoded_results in decoded_results.iteritems():
            imgpaths = ballots[ballotid]
            for i, (bitstring, is_flipped, bit_locations) in enumerate(decoded_results):
                imgpath = imgpaths[i]
                flip_map[imgpath] = is_flipped
                if not bitstring:
                    print "..error on: {0}".format(imgpath)
                    err_imgpaths.append(imgpath)
                else:
                    img2decoding[imgpath] = (bitstring,)
                    for bit_value, boxes in bit_locations.iteritems():
                        for box in boxes:
                            tup = (imgpath, box, counter)
                            bbs_map.setdefault(bit_value, []).append(tup)
                            counter += 1
        return img2decoding, flip_map, bbs_map, err_imgpaths, ioerr_imgpaths

    def partition_ballots(self, img2decoding, verified_results, manual_labeled):
        """
        Given the user-verified (and corrected) results of decode_ballots,
        output the partitioning.

        Input:
            img2decoding     : {imgpath: (str decoding_0, ...)}
            verified_results : {bit_value: [(str imgpath, (x1,y1,x2,y2), userinfo), ...]}
                If this is empty/None, then the user did not do barcode overlay
                verification, so just use the img2decoding information.
            manual_labeled   : {imgpath: bitstring}
        Output:
            partitions   : stores the partitioning as:
                           {partitionID: [ballotid_i, ...]}
            img2decoding : stores barcode strings for each image as:
                           {imgpath: [bitstring_i, ...]}
            imginfo_map  : stores info for image (currently only page for partitioning)
        """
        '''
        TODO: Storing metadata on each barcode mark (the 'verified_results' dict)
              ends up consuming a lot of memory for large elections.
              As a stop-gap: If the user does not want to do barcode overlay verification,
              then we can simply not store the data about each barcode mark, and just
              use the img2decoding data structure to perform the partitioning.
              This ES&S decoder currently doesn't do this, which shouldn't
              cause any crashes, but may run into memory issues on large
              elections.
        '''
        partitions = {}
        img2decoding = {}
        imginfo_map = {}
        img_bc_temp = {}
        for bit_value, tups in verified_results.iteritems():
            for (imgpath, (x1,y1,x2,y2), userinfo) in tups:
                img_bc_temp.setdefault(imgpath, []).append((bit_value, y1))
        # img_decoded_map: {str imgpath: str decoding}
        img_decoded_map = es_s.build_bitstrings(img_bc_temp, bits)
        img2bal = pickle.load(open(self.proj.image_to_ballot, 'rb'))
        attrs2partitionID = {} # {('precinct', 'language', 'party'): int partitionID}
        curPartitionID = 0
        for imgpath, decoding in dict(img_decoded_map.items() + manual_labeled.items()).iteritems():
            img2decoding[imgpath] = decoding
            imginfo = es_s.get_info([decoding])
            imginfo_map[imgpath] = imginfo
            tag = decoding # TODO: change once we know meaning of barcode
            partitionid = attrs2partitionID.get(tag, None)
            if partitionid == None:
                partitionid = curPartitionID
                attrs2partitionID[tag] = curPartitionID
                curPartitionID += 1
            ballotid = img2bal[imgpath]
            partitions.setdefault(partitionid, set()).add(ballotid)
        for partitionid, ballotid_set in partitions.iteritems():
            partitions[partitionid] = sorted(list(ballotid_set))
        return partitions, img2decoding, imginfo_map

    def __repr__(self):
        return 'ES&SVendor()'
    def __str__(self):
        return 'ES&SVendor()'


def _do_decode_ballots(ballots, mark_path, queue=None):
    """ 
    Decode ES&S barcode for all ballots
    Input:
        ballots   : {int ballotID: [imgpath_side0, ...]}.
        mark_path : path to example timing mark representing '1' in bitstring
        queue     : used for multiprocessing
    Output:
        results: {ballotid: [(bitstring, is_flipped, bit_locations), ...]}
    """

    try:
        mark = cv.LoadImage(mark_path, cv.CV_LOAD_IMAGE_GRAYSCALE)
        results = {}
        for ballotid, imgpaths in ballots.iteritems():
            balresults = []
            for imgpath in imgpaths:
                bitstring, is_flipped, bit_locations = es_s.decode(imgpath, mark, bits)
                balresults.append((bitstring, is_flipped, bit_locations))
            results[ballotid] = balresults
            if queue:
                queue.put(True)
        return results
    except:
        traceback.print_exc()

def decode_ballots(ballots, mark_path, manager, queue):
    """ 
    Decode ES&S barcode for all ballots by calling multiprocessing module.
    Input:
        ballots   : {int ballotID: [imgpath_side0, ...]}
        mark_path : path to example timing mark representing '1' in bitstring
        manager   : used for multiprocessing
        queue     : used for multiprocessing
    Output:
        decoded_results: {ballotid: [(bitstring, is_flipped, bit_locations), ...]}
    """

    try:
        decoded_results = partask.do_partask(_do_decode_ballots,
                                             ballots,
                                             _args=mark_path,
                                             combfn='dict',
                                             manager=manager,
                                             pass_queue=queue,
                                             N=None)
        print 'finished decoding:'
        return decoded_results
    except:
        traceback.print_exc()
        return None
