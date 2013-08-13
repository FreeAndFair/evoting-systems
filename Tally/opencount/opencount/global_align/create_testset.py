import sys, os, pdb, time, cPickle as pickle, argparse, math
from os.path import join as pathjoin

import numpy as np, scipy.misc, scipy.ndimage, cv

sys.path.append('..')
from projconfig_new.project_panel import Project

"""
A script that generates a synthetic testset to evaluate alignment
algorithms.
For each input voted ballot image, varying amounts of translation,
rotation, noise, and illumination differences are added to the image
and saved to disk.
"""

DESCRIPTION = """Creates a synthetic testset to allow quantitative
evaluation of global alignment strategies.
For each image Isrc, we perturb it with varying amounts of rotation,
translation, noise, intensity-modifications.
"""

def fastFlip(I):
    Icv=cv.fromarray(np.copy(I))
    I1cv=cv.CreateMat(I.shape[0],I.shape[1],Icv.type)
    cv.Flip(Icv,I1cv,-1)
    Iout=np.asarray(I1cv)
    return Iout

def create_testset(imgpaths, outdir, args,
                   X, Y, STEP_TRANS_X, STEP_TRANS_Y,
                   THETA, STEP_ROT,
                   MEAN, STD, BRIGHT_AMT, BRIGHT_STEP,
                   img2flip=None):
    """ Synthetically-perturbs each image I in IMGPATHS, then stores 
    it to OUTDIR.
    """
    def saveimg(I, idx, x, y, theta, bright_amt):
        if args.dontsave:
            return None
        rootdir = os.path.join(outdir, str(idx))
        if not os.path.exists(rootdir):
            os.makedirs(rootdir)
        outname = "img{0}_{1}_{2}_{3}.png".format(x, y, theta, bright_amt)
        outpath = os.path.join(rootdir, outname)
        scipy.misc.imsave(outpath, I)
        return outpath
    cnt = 0
    src2dsts = {} # maps {str src_imP: [(str dst_imP, x, y, theta, bright_amt), ...]
    dst2src = {} # maps {str dst_imP: str src_imP}
    # Type-convert some floats to ints, just in case
    X, Y, STEP_TRANS_X, STEP_TRANS_Y = int(X), int(Y), int(STEP_TRANS_X), int(STEP_TRANS_Y)

    t_start = time.time()
    t_prev = time.time()
    N = len(imgpaths)
    step = N / 10 # Update every 10%
    cur_i = 0
    def update_status():
        if cur_i == 0:
            return
        t_cur = time.time()
        dur_step = t_cur - t_prev
        n_remain = N - cur_i
        try:
            est_time = ((dur_step / float(step)) * n_remain) / 60.0 # In Minutes
            print "...{0:.2f}% done... ({1} images left, {2:.4f} min. left)...".format(100.0 * (cur_i / float(N)),
                                                                                       n_remain,
                                                                                       est_time)
            return True
        except ZeroDivisionError as e:
            print "...{0:.2f}% done... ({1} images left))...".format(100.0 * (cur_i / float(N)),
                                                                     n_remain)
            return True
        return False

    for idx, imgpath in enumerate(sorted(imgpaths)):
        did_update = update_status()
        if did_update:
            t_prev = time.time()
        if not args.dontsave:
            I = scipy.misc.imread(imgpath, flatten=True)
        else:
            I = np.zeros((2*(Y+1), 2*(X+1)), dtype='uint8')
        if I != None and img2flip != None and img2flip[imgpath]:
            I = fastFlip(I)
        for x in range(-X, X, STEP_TRANS_X):
            Ix = np.zeros(I.shape, dtype=I.dtype)
            if x == 0:
                Ix[:,:] = I
            elif x < 0:
                Ix[:,:x] = I[:,-x:]
            else:
                Ix[:,x:] = I[:,:-x]
            for y in range(-Y, Y, STEP_TRANS_Y):
                Ixy = np.zeros(I.shape, dtype=I.dtype)
                if y == 0:
                    Ixy[:,:] = Ix
                elif y < 0:
                    Ixy[:y,:] = Ix[-y:,:]
                else:
                    Ixy[y:,:] = Ix[:-y,:]
                for theta in np.linspace(-THETA, THETA, num=((2*THETA / STEP_ROT)+1), endpoint=True):
                    if not args.dontsave:
                        Ixyt = scipy.ndimage.rotate(Ixy, theta, reshape=False)
                    else:
                        Ixyt = Ixy
                    brightamt_iter = np.linspace(-BRIGHT_AMT, BRIGHT_AMT, num=(2*BRIGHT_AMT / BRIGHT_STEP), endpoint=True) if BRIGHT_AMT != None else [0]
                    for bright_amt in brightamt_iter:
                        Ixytb = Ixyt + bright_amt
                        if MEAN != None and STD != None:
                            noise = np.random.normal(MEAN, STD, size=(Ixytb.shape))
                            Ixytb += noise
                        Ixytb[np.where(Ixytb < 0)] = 0
                        Ixytb[np.where(Ixytb > 255)] = 255
                        outpath = saveimg(Ixytb, idx, x, y, theta, bright_amt)
                        src2dsts.setdefault(imgpath, []).append((outpath, x, y, theta, bright_amt))
                        dst2src[outpath] = imgpath
                        cnt += 1
        cur_i += 1
    return cnt, src2dsts, dst2src

def parse_args():
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    ## Positional Arguments
    parser.add_argument("imgsdir", help="Directory of images \
to create the testset from. (Alternate: imgpath, or OpenCount projdir)")
    parser.add_argument("outdir", help="Output path to store testset.")
    ## Optional Arguments
    parser.add_argument("--as_projdir", help="If given, then treat IMGSDIR positional \
argument as a directory to an OpenCount project directory. Sample N ballots from \
each M groups to create the testset from. If N/M is -1, then do all ballots/groups.",
                        nargs=2, type=int,
                        metavar=("N", "M"),
                        default=None)
    parser.add_argument("--side", help="Specify which ballot side to use, in conjunction \
with --as_projdir. 0 is front, 1 is back, etc.",
                        type=int)

    parser.add_argument("--dontsave", help="Don't save the warped images to OUTDIR. \
Instead, the eval_align.py script will load the src img, warp it, and then perform \
the alignment.",
                        action="store_true", default=False)

    parser.add_argument("--trans", help="Adds horizontal/vertical amount of translation in the ranges \
[-X, X], [-Y, Y] with a step size given by STEPX/STEPY. Default: [X=12,Y=12,STEPX=4,STEPY=4]",
                        nargs=4, type=float,
                        metavar=("X", "STEPX", "Y", "STEPY"),
                        default=(12, 6, 12, 6))
    parser.add_argument("--rot", help="Adds an amount of rotation in the range [-THETA, THETA] with step \
size given by STEP. Default: [THETA=1.2,STEP=0.4]",
                        nargs=2, type=float,
                        metavar=("THETA", "STEP"),
                        default=(0.6, 0.4))
    parser.add_argument("--brightness", help="Adds a constant amount to each pixel intensity value (saturating \
at 0 and 255) in the range [-AMT, AMT] with stepsize STEP.",
                        nargs=2, type=float,
                        metavar=("AMT", "STEP"),
                        default=(None, None))
    parser.add_argument("--noise", help="Adds noise to the image by sampling from a gaussian distribution \
with mean MEAN, std deviation STD.",
                        nargs=2, type=float,
                        metavar=("MEAN", "STD"),
                        default=(None, None))

    parser.add_argument("--alt_voteddir", help="(For use w/ --as_projdir) Use an alternate root voteddir \
directory. Bit of a one-off feature for Eric to apply grouping results to a voteddir whose images were \
compressed.")

    args = parser.parse_args()
    imgsdir, outdir = args.imgsdir, args.outdir

    X, STEP_TRANS_X, Y, STEP_TRANS_Y = args.trans
    THETA, STEP_ROT = args.rot
    BRIGHT_AMT, BRIGHT_STEP = args.brightness
    MEAN, STD = args.noise
    ALT_VOTEDDIR = args.alt_voteddir

    return (X, Y, STEP_TRANS_X, STEP_TRANS_Y, THETA, STEP_ROT, MEAN, STD,
            BRIGHT_AMT, BRIGHT_STEP,
            args,
            imgsdir, outdir, ALT_VOTEDDIR)

def main():
    X, Y, STEP_TRANS_X, STEP_TRANS_Y, THETA, STEP_ROT, MEAN, STD, BRIGHT_AMT, BRIGHT_STEP, args, imgsdir, outdir, alt_voteddir = parse_args()
    
    if not args.as_projdir:
        imgpaths = []
        if not os.path.isdir(imgsdir):
            imgpaths = [imgsdir]
        else:
            for dirpath, dirnames, filenames in os.walk(imgsdir):
                for imgname in [f for f in filenames if f.lower().endswith('.png')]:
                    imgpath = os.path.join(dirpath, imgname)
                    imgpaths.append(imgpath)
        img2flip_ = None
    else:
        imgpaths = []
        img2flip_ = {}
        projdir = imgsdir
        grp2bals = pickle.load(open(pathjoin(projdir, 'group_to_ballots.p')))
        bal2imgs = pickle.load(open(pathjoin(projdir, 'ballot_to_images.p')))
        img2flip_proj = pickle.load(open(pathjoin(projdir, 'image_to_flip.p')))
        img2page = pickle.load(open(pathjoin(projdir, 'image_to_page.p')))
        # TARGET_LOCS_MAP: maps {int groupID: {int page: [CONTEST_i, ...]}}, where each
        #     CONTEST_i is: [contestbox, targetbox_i, ...], where each
        #     box := [x1, y1, width, height, id, contest_id]
        grp2targets = pickle.load(open(pathjoin(projdir, 'target_locs_map.p')))

        def get_proj_voteddir():
            proj = pickle.load(open(pathjoin(projdir, 'proj.p')))
            return proj.voteddir
        def has_targets(grpid, side):
            return len(grp2targets[grpid].get(side, [])) >= 1

        voteddir_root = get_proj_voteddir()

        grp2bals_items = sorted(grp2bals.items(), key=lambda t: -len(t[1]))
        LIMIT_BAL, LIMIT_GRP = args.as_projdir
        n_grps = 0
        for i, (grpid, balids) in enumerate(grp2bals_items):
            if LIMIT_GRP != -1 and n_grps >= LIMIT_GRP:
                break
            if args.side != None and not has_targets(grpid, args.side):
                continue # Avoid empty groups counting towards N_GRPS
            for j, balid in enumerate(balids):
                if LIMIT_BAL != -1 and j >= LIMIT_BAL:
                    break
                bal_imgpaths = sorted(bal2imgs[balid], key=lambda imP: img2page[imP])
                if not alt_voteddir:
                    for side, imgpath in enumerate(bal_imgpaths):
                        if (args.side != None and args.side != side) or not has_targets(grpid, side):
                            continue # This isn't a side we care about
                        imgpaths.append(imgpath)
                        img2flip_[imgpath] = img2flip_proj[imgpath]
                else:
                    for side, imgpath_old in enumerate(bal_imgpaths):
                        if (args.side != None and args.side != side) or not has_targets(grpid, side):
                            continue # This isn't a side we care about
                        rp = os.path.relpath(os.path.abspath(imgpath_old), os.path.abspath(voteddir_root))
                        imgpath_new = pathjoin(alt_voteddir, rp)
                        imgpaths.append(imgpath_new)
                        img2flip_[imgpath_new] = img2flip_proj[imgpath_old]
            n_grps += 1

    if not os.path.exists(outdir):
        os.makedirs(outdir)
    if args.dontsave:
        print "(Info) --dontsave was passed. Not saving any images to outdir."

    f_info = open(pathjoin(outdir, 'info.txt'), 'w')
    print >>f_info, "X: {0}  STEP_X: {1}".format(X, STEP_TRANS_X)
    print >>f_info, "Y: {0}  STEP_Y: {1}".format(Y, STEP_TRANS_Y)
    print >>f_info, "THETA: {0}  STEP_THETA: {1}".format(THETA, STEP_ROT)
    print >>f_info, "NOISE_MEAN: {0}  NOISE_STD: {1}".format(MEAN, STD)
    print >>f_info, "BRIGHT_AMT: {0}  BRIGHT_AMT: {1}".format(BRIGHT_AMT, BRIGHT_STEP)
    print >>f_info, sys.argv
    f_info.close()

    print "...Creating testset from {0} to {1}...".format(imgsdir, outdir)
    t = time.time()
    cnt, src2dsts, dst2src,  = create_testset(imgpaths, outdir, args,
                                              X, Y, STEP_TRANS_X, STEP_TRANS_Y,
                                              THETA, STEP_ROT,
                                              MEAN, STD, 
                                              BRIGHT_AMT, BRIGHT_STEP,
                                              img2flip=img2flip_)
    dur = time.time() - t
    print "...Done ({0}s). Saved {1} images to {2}.".format(dur, cnt, outdir)
    pickle.dump(src2dsts, open(os.path.join(outdir, 'src2dsts.p'), 'wb'))
    pickle.dump(dst2src, open(os.path.join(outdir, 'dst2src.p'), 'wb'))
    pickle.dump(img2flip_, open(os.path.join(outdir, 'src2flip.p'), 'wb'))
        
if __name__ == '__main__':
    main()
