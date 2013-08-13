import sys, time

import numpy as np, scipy.misc, cv
import wx

def main():
    args = sys.argv[1:]
    imgpath = args[0]

    wximg = wx.Image(imgpath, wx.BITMAP_TYPE_ANY)
    
    w, h = wximg.GetWidth(), wximg.GetHeight()

    '''
    wximg_gray = wximg.ConvertToGreyscale()

    wximg_data = wximg_gray.GetDataBuffer()

    newdata = black_half(wximg_data, wximg.GetWidth(), wximg.GetHeight())

    wximg_new = wx.EmptyImage(wximg.GetWidth(), wximg.GetHeight())
    wximg_new.SetDataBuffer(newdata)
    wximg_new.SaveFile("foobar.png", wx.BITMAP_TYPE_PNG)

    pdb.set_trace()
    '''

    t = time.time()
    cv_img = wximg_to_cv(wximg, flatten=True)
    dur = time.time() - t
    print "...Time elapsed cvFlatten:", dur

    t = time.time()
    np_img = wximg_to_np(wximg, flatten=True)
    dur = time.time() - t
    print "...Time elapsed npFlatten:", dur

    t = time.time()
    cv_imgColor = wximg_to_cv(wximg)
    dur = time.time() - t
    print "...Time elapsed cvColor:", dur

    t = time.time()
    np_imgColor = wximg_to_np(wximg)
    dur = time.time() - t
    print "...Time elapsed npColor:", dur

    cv.SaveImage("_cvimg.png", cv_img)
    scipy.misc.imsave("_npimg.png", np_img)
    cv.SaveImage("_cvimgColor.png", cv_imgColor)
    scipy.misc.imsave("_npimgColor.png", np_imgColor)

def wximg_to_np(wximg, flatten=False):
    """ Converts a WxImage to a numpy array, with optional conversion
    to Grayscale (single channel).
    """
    w, h = wximg.GetWidth(), wximg.GetHeight()
    #wximg = wximg.Copy()
    if flatten:
        wximg = wximg.ConvertToGreyscale()
    #data = wximg.GetDataBuffer()
    #pdb.set_trace()
    #npdata = np.frombuffer(data, dtype="u1")
    #npdata = np.frombuffer(data, dtype='uint8')
    npdata = np.fromstring(wximg.GetData(), dtype='uint8')
    #pdb.set_trace()
    npdata = npdata.reshape(h, w, 3)
    if flatten:
        # WxImage data buffers always hold RGB (3) channels.
        # Only return one of the channels (all equiv anyways, due to
        # the prior ConvertToGreyscale() call. 
        return npdata[:,:,0]
    return npdata

def wximg_to_cv(wximg, flatten=False):
    """ Converts a WxImage to a OpenCV IplImage, with optional conversion
    to Grayscale (single channel).
    """
    w, h = wximg.GetWidth(), wximg.GetHeight()
    #wximg = wximg.Copy()
    if flatten:
        wximg = wximg.ConvertToGreyscale()
    #data = wximg.GetData()

    #cv_im = cv.CreateImage((w, h), cv.IPL_DEPTH_8U, 3)
    #cv.SetData(cv_im, data)

    #cv_mat = cv.CreateMat(h,w, cv.CV_8UC3)
    #cv.SetData(cv_mat, data)

    #cv_mathead= cv.CreateMatHeader(h, w, cv.CV_8UC3)
    #cv.CreateData(cv_mathead)
    #cv.SetData(cv_mat, data)

    cv_mat = cv.CreateMat(h, w, cv.CV_8UC3)
    cv.SetData(cv_mat, wximg.GetData())

    #cv.Copy(data, cv_mat)
    if flatten:
        #cv.SetImageCOI(cv_im, 1)
        #res = cv.CreateImage((w,h), cv.IPL_DEPTH_8U, 1)
        #cv.Copy(cv_im, res)
        #return res
        res = cv.CreateMat(h,w,cv.CV_8UC1)
        cv.Split(cv_mat, res, None, None, None)
        return res
    else:
        return cv_mat

main()
