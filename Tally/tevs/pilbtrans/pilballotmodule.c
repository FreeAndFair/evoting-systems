#include <Python.h>
#include <Imaging.h>
#include <stdio.h>

static  PyObject *
bias (PyObject* self, PyObject* args)
{
  Imaging imIn, imOut;
  int x, y; 
  long idIn, idOut;
  int multiplier;
  if (!PyArg_ParseTuple(args, "lli", &idIn, &idOut,&multiplier))
    return NULL;
  printf("Multiplier %d\n",multiplier);
  /* get image */
  imIn = (Imaging) idIn;
  imOut = (Imaging) idOut;
  
  /* check modes, sizes, etc */
  
  /* do some processing */	 
  
  for (y = 0; y < imIn->ysize; y++) {
    UINT8* in = imIn->image[y];
    UINT8* out = imOut->image[y];
    for (x = 0; x < (imIn->xsize*multiplier); x+=multiplier)
      
      if (*(in+x)<128){
	*(out+x) = 128;
	if (multiplier == 4){
	  *(out+x+1) = 128;
	  *(out+x+2) = 128;
	  *(out+x+3) = 128;
	}
      }
      else { 
	*(out+x) = *(in+x);
	if (multiplier == 4){
	  *(out+x+1) = *(in+x+1);
	  *(out+x+2) = *(in+x+2);
	  *(out+x+3) = *(in+x+3);
	}
      }
  }
  
  Py_INCREF(Py_None);
  return Py_None;
}

static  PyObject *
stats (PyObject* self, PyObject* args)
{
  Imaging imIn;
  PyObject *retlist;
  int x, y;
  int multiplier;
  int lowcount = 0;
  int highcount = 0;
  long idIn;
  if (!PyArg_ParseTuple(args, "li", &idIn, &multiplier))
    return NULL;
  
  /* get image */
  imIn = (Imaging) idIn;
  
  /* do some processing */
  for (y = 0; y < imIn->ysize; y++) {
    UINT8* in = imIn->image[y];
    for (x = 0; x < (imIn->xsize*multiplier); x+=multiplier) {
      //red channel only for RGB, RGBA
      if (*(in+x) < 128) 
	lowcount++;
      else 
	highcount++;
    }

    
  }
  printf("imIn->ysize %d xsize %d area %d\n",
	 imIn->ysize,imIn->xsize,imIn->ysize*imIn->xsize);
  retlist = Py_BuildValue("ii",lowcount,highcount);
  return retlist;
}

static PyMethodDef PilballotMethods[] = {
        {"bias",  bias, METH_VARARGS,
     "Prove you can read an image and write a changed version."},
        {"stats",  stats, METH_VARARGS,
     "Return number of pixels with intensity < 128, then >= 128."},
    {NULL, NULL, 0, NULL}        /* Sentinel */
};


PyMODINIT_FUNC
initpilballot(void)
{
    PyObject *m;

    m = Py_InitModule("pilballot", PilballotMethods);
    if (m == NULL)
        return;
    return;
}
