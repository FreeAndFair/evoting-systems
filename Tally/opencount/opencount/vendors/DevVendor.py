import sys, os, cPickle as pickle
from Vendor import Vendor

class DevVendor(Vendor):
    """ A simple Vendor that outputs groups according to directory structure, e.g.:
    Group0:
        voteddir/styleA/*
    Group1:
        voteddir/styleB/*
    ...
    """
    def __init__(self, proj):
        self.proj = proj

    def decode_ballots(self, ballots, manager=None, queue=None, skipVerify=True):
        """
        Input:
            dict BALLOTS: {int ballotID: [imgpath_side0, ...]}.
        Output:
            (dict IMG2DECODING,
             dict FLIP_MAP,
             dict VERIFYPATCH_BBS,
             list ERR_IMGPATHS,
             list IOERR_IMGPATHS)
        """
        img2decoding = {}
        img2flip = {}
        verifypatch_bbs = None
        
        parentdir2decode = {} # maps {str parentdirname: int outdecode}
        cur_outdec = 0
        for balid, imgpaths in ballots.iteritems():
            parentdir = os.path.split(os.path.split(imgpaths[0])[0])[1]
            if parentdir not in parentdir2decode:
                parentdir2decode[parentdir] = cur_outdec
                cur_outdec += 1
            for imgpath in imgpaths:
                img2decoding[imgpath] = str(parentdir2decode[parentdir])
                img2flip[imgpath] = False
            
        return img2decoding, img2flip, verifypatch_bbs, [], []

    def partition_ballots(self, img2decoding, verified_results, manual_labeled):
        """
        Input:
            dict IMG2DECODING: {str imgpath: (str decoding_0, ...)}
            dict VERIFIED_RESULTS: {str bc_val: [(str imgpath, (x1,y1,x2,y2), userinfo), ...]}
            dict MANUAL_LABELED: {str imgpath: (str label_i, ...)}
                Stores the decoded barcode(s) of any images that the user
                manually entered.
                This maps to a /tuple/ of strings, because there may be
                multiple barcodes on a given image.
        Output:
            (dict PARTITIONS, 
             dict IMG2DECODING,
             dict IMAGE_INFO)
        """
        part2bals = {} # maps {int partitionid: [int balid_0, ...]}
        imginfo = {} # maps {str imgpath: {str PROPNAME: str PROPVAL}}

        history = set() # set([int balid, ...])
        dec2partid = {}
        cur_partid = 0

        bal2imgs = pickle.load(open(self.proj.ballot_to_images, 'rb'))
        img2bal = pickle.load(open(self.proj.image_to_ballot, 'rb'))

        for imgpath, dec in img2decoding.iteritems():
            balid = img2bal[imgpath]
            if balid in history:
                continue
            history.add(balid)
            if dec not in dec2partid:
                dec2partid[dec] = cur_partid
                cur_partid += 1
            part2bals.setdefault(dec2partid[dec], []).append(balid)

        for balid, imgpaths in bal2imgs.iteritems():
            for i, imgpath in enumerate(sorted(imgpaths)):
                imginfo[imgpath] = {'page': i}

        return part2bals, img2decoding, imginfo

    def __repr__(self):
        return 'DevVendor()'
    def __str__(self):
        return 'DevVendor()'
