import sys, os, Queue
import cPickle as pickle
import numpy as np

from os.path import join as pathjoin

import pixel_reg.doExtract as doExtract

"""
Yolo bad target extract paths:

yolo_s2_074/yolo_s2_074-020.png
yolo_s2_074/yolo_s2_074-044.png
yolo_s3_086/yolo_s3_086-032.png
yolo_s2_074/yolo_s2_074-083.png
yolo_s2_074/yolo_s2_074-007.png
yolo_s2_074/yolo_s2_074-027.png
yolo_s2_074/yolo_s2_074-012.png
yolo_s3_086/yolo_s3_086-035.png
yolo_s3_071/yolo_s3_071-099.png
yolo_s2_074/yolo_s2_074-046.png

yolo_s4_006/yolo_s4_006-219.png
    Only the state senator contest targets were misaligned

Usage:
    To reproduce Yolo bad target extraction:

    python do_single_textract.py /home/arya/opencount/opencount/projects/Yolo_2012 \
/media/data1/audits2012_straight/yolo/votedballots/yolo_s2_074/yolo_s2_074-020.png bad_out

Or, as a super-simple shortcut, the following is equivalent:
  
    python do_single_textract.py bad_out

This will do target extraction on yolo_s2_074-020.png, and dump it to bad_out/.
"""
def isimgext(f):
    return os.path.splitext(f)[1].lower() in ('.jpg', '.png', '.jpeg')

def main():
    args = sys.argv[1:]
    if len(args) == 1:
        outdir = args[0]
        projdir = '/home/arya/opencount/opencount/projects/Yolo_2012'
        votedpath = '/media/data1/audits2012_straight/yolo/votedballots/yolo_s2_074/yolo_s2_074-020.png'
    else:
        projdir = args[0]
        votedpath = args[1]
        if isimgext(votedpath):
            imgpaths = [votedpath]
        else:
            imgpaths = []
            for dirpath, dirnames, filenames in os.walk(votedpath):
                for imgname in [f for f in filenames if isimgext(f)]:
                    imgpaths.append(os.path.join(dirpath, imgname))
            
        outdir = args[2]
    
    t_imgs = pathjoin(outdir, 'extracted')
    t_diff = pathjoin(outdir, 'extracted_diff')
    t_meta = pathjoin(outdir, 'extracted_metadata')
    b_meta = pathjoin(outdir, 'ballot_metadata')
    try: os.makedirs(t_imgs)
    except: pass
    try: os.makedirs(t_diff)
    except: pass
    try: os.makedirs(t_meta)
    except: pass
    try: os.makedirs(b_meta)
    except: pass

    bal2group = pickle.load(open(pathjoin(projdir, 'ballot_to_group.p'), 'rb'))
    group2bals = pickle.load(open(pathjoin(projdir, 'group_to_ballots.p'), 'rb'))
    b2imgs = pickle.load(open(pathjoin(projdir, 'ballot_to_images.p'), 'rb'))
    img2b = pickle.load(open(pathjoin(projdir, 'image_to_ballot.p'), 'rb'))
    img2page = pickle.load(open(pathjoin(projdir, 'image_to_page.p'), 'rb'))
    img2flip = pickle.load(open(pathjoin(projdir, 'image_to_flip.p'), 'rb'))
    target_locs_map = pickle.load(open(pathjoin(projdir, 'target_locs_map.p'), 'rb'))
    group_exmpls = pickle.load(open(pathjoin(projdir, 'group_exmpls.p'), 'rb'))

    proj = pickle.load(open(pathjoin(projdir, 'proj.p'), 'rb'))
    voteddir_root = proj.voteddir
    
    # 0.) Set up job
    jobs = []
    def get_bbs(groupID, target_locs_map):
        bbs_sides = []
        boxes_sides = target_locs_map[groupID]
        for side, contests in sorted(boxes_sides.iteritems(), key=lambda t: t[0]):
            bbs = np.empty((0, 5))
            for contest in contests:
                cbox, tboxes = contest[0], contest[1:]
                for tbox in tboxes:
                    # TODO: Temporary hack to re-run target extract
                    # on SantaCruz, without re-doing SelectTargets
                    x1 = tbox[0] + 33
                    y1 = tbox[1]
                    x2 = tbox[0] + tbox[2] - 23
                    y2 = tbox[1] + tbox[3]
                    id = tbox[4]
                    bb = np.array([y1, y2, x1, x2, id])
                    bbs = np.vstack((bbs, bb))
            bbs_sides.append(bbs)
        return bbs_sides

    for votedpath in imgpaths:
        ballotid = img2b[votedpath]
        groupID = bal2group[ballotid]

        bbs = get_bbs(groupID, target_locs_map)
        # 1.a.) Create 'blank ballots'. This might not work so well...
        exmpl_id = group_exmpls[groupID][0]
        blankpaths = b2imgs[exmpl_id]
        blankpaths_ordered = sorted(blankpaths, key=lambda imP: img2page[imP])
        blankpaths_flips = [img2flip[blank_imP] for blank_imP in blankpaths_ordered]

        imgpaths = b2imgs[ballotid]
        imgpaths_ordered = sorted(imgpaths, key=lambda imP: img2page[imP])
        imgpaths_flips = [img2flip[imP] for imP in imgpaths_ordered]
        job = [blankpaths_ordered, blankpaths_flips, bbs, imgpaths_ordered, imgpaths_flips, 
               t_imgs, t_diff, t_meta, b_meta, voteddir_root, Queue.Queue(), Queue.Queue()]
        jobs.append(job)

    '''
    res = doExtract.convertImagesSingleMAP(bal2imgs, tpl2imgs, bal2tpl, img2bal,
                                           csvPattern, 
                                           t_imgs, t_meta, b_meta,
                                           pathjoin(projdir, 'quarantined.csv'),
                                           lambda: False,
                                           None)
    '''
    for job in jobs:
        doExtract.convertImagesWorkerMAP(job)
    
if __name__ == '__main__':
    main()
