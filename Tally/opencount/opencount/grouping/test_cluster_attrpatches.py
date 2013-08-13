import sys, os

import scipy.misc
import cluster_imgs

def is_img_ext(p):
    return os.path.splitext(p.lower())[1] in ('.png', '.jpg', '.jpeg')

def main():
    args = sys.argv[1:]
    imgsdir = args[0]
    outdir = args[1]
    election = args[2]
    imgpaths = []
    if election == 'marin':
        bb_map = {}
    else:
        bb_map = None
    for dirpath, dirnames, filenames in os.walk(imgsdir):
        for imgname in [f for f in filenames if is_img_ext(f)]:
            if 'mail-14' in imgname:
                print "Idx for mail-14:", len(imgpaths)
            elif 'vbm-28' in imgname:
                print "Idx for vbm-28:", len(imgpaths)
            imgpaths.append(os.path.join(dirpath, imgname))
            if election == 'marin':
                bb_map[os.path.join(dirpath, imgname)] = (137, 173, 37, 201)
    
    #random.shuffle(imgpaths)
    #clusters = cluster_imgs.cluster_imgs_kmeans_alignerr(imgpaths, bb_map=bb_map)
    #clusters = cluster_imgs.cluster_imgs_kmeans_mine(imgpaths, distfn_method='vardiff', 
    #                                                 centroidfn_method='median', 
    #                                                 bb_map=bb_map)
    clusters = cluster_imgs.kmeans_2D(imgpaths, distfn_method='vardiff', k=4,
                                      do_align=True,
                                      do_edgedetect=False,
                                      bb_map=bb_map)
    '''
    clusters = cluster_imgs.kmediods_2D(imgpaths, distfn_method='vardiff', k=4,
                                        do_align=True,
                                        do_edgedetect=False,
                                        bb_map=bb_map)
    '''
    #clusters = cluster_imgs.cluster_imgs_kmeans(imgpaths, bb_map=bb_map)
    #clusters = cluster_imgs.cluster_imgs_pca_kmeans(imgpaths, bb_map=bb_map)
    #clusters = cluster_imgs.cluster_imgs_hag(imgpaths, bb_map=bb_map)
    if bb_map == None:
        bb_map = {}
    for cluster, imgpaths in clusters.iteritems():
        #overlay, minimg, maximg = make_overlays.overlay_im(imgpaths, include_min_max=True)
        #minimg, maximg = make_overlays.make_minmax_overlay(imgpaths)
        
        outrootdir = os.path.join(outdir, str(cluster))
        try:
            os.makedirs(outrootdir)
        except:
            pass
        for imgpath in imgpaths:
            img = scipy.misc.imread(imgpath, flatten=True)
            if imgpath in bb_map:
                bb = bb_map[imgpath]
                img = img[bb[0]:bb[1], bb[2]:bb[3]]
            scipy.misc.imsave(os.path.join(outrootdir, os.path.split(imgpath)[1]), img)

        #scipy.misc.imsave(os.path.join(outrootdir, 'min.png'), minimg)
        #scipy.misc.imsave(os.path.join(outrootdir, 'max.png'), maximg)

if __name__ == '__main__':
    main()

# Marin BallotType: (37, 137), (201, 173)
