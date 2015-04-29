#include <stdio.h>
#include <Python.h>
#include <Imaging.h> //The Python Imaging library

#define max(A,B)	( (A) > (B) ? (A):(B)) 
#define min(A,B)	( (A) < (B) ? (A):(B)) 
/* BALLOT ANALYSIS (works with RGB only) */
/* return a list of vertical offsets at which a running average */
/* switches from white to medium to black */
static inline PyObject*
getchanges(Imaging im, int xtop, int xbottom, int dpi)
{
  int last60reds;
  int x,y,x20ago;
  int laststate;

  int lastappendedy;
  int newstate;
  PyObject *item;
  PyObject *list;
  
  UINT8 *p;
  UINT8 *p20above;

  lastappendedy = 0;
  laststate = 0;//BLACKSTATE;
  newstate = 0;//BLACKSTATE;
    
  list = PyList_New(0);
  last60reds = 0;
  for (y = 0; y < im->ysize; y++){
    x = (int) ( (((float)y/im->ysize)*xbottom)
		+  (((float)(im->ysize-y)/im->ysize)*xtop));
    x20ago = (int) ( (((float)(y-20)/im->ysize)*xbottom)
		     +  (((float)(im->ysize-(y-20))/im->ysize)*xtop));
    p = (UINT8 *)&im->image32[y][x];
    last60reds += *p;
    p = (UINT8 *)&im->image32[y][x+1];
    last60reds += *p;
    p = (UINT8 *)&im->image32[y][x+2];
    last60reds += *p;
    if (y >= 20){
      p20above = (UINT8 *)&im->image32[y-20][x20ago];
      last60reds -= *p20above;
      p20above = (UINT8 *)&im->image32[y-20][x20ago+1];
      last60reds -= *p20above;
      p20above = (UINT8 *)&im->image32[y-20][x20ago+2];
      last60reds -= *p20above;
    }
    if (last60reds > (224*60)){
      newstate = 2;//WHITESTATE;
    }
    else if (last60reds > (64*60)){
      newstate = 1;//GRAYSTATE;
    }
    else {
      newstate = 0;//BLACKSTATE;
    }
    if (newstate != laststate){
      laststate = newstate;
      // keep the y from 10 back 
      if ((y<dpi) || (y>(im->ysize - dpi))){
	continue;
      }
      /* if you don't filter out transitions that happen within 1/6",
	 you sometimes get a nonexistent gray on the way 
	 from black to white and vice versa; remove it in Python,
         knowing that immediate 0->1->2 or 2->1->0 does not occur */

      item = Py_BuildValue("[ii]",newstate,y-10);
      lastappendedy = y;
      if (!item){
	Py_DECREF(list);
	return NULL;
      }
      PyList_Append(list,item);

    }
  }
  return list;
}


/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject*
gethartlandmarks(Imaging im, int dpi, int need_vops)
{
  UINT8 *p;
  int found_topline_left = 0;
  int found_topline_right = 0;
  int found_bottomline_left = 0;
  int found_bottomline_right = 0;
  int found_leftline_top = 0;
  int found_leftline_bottom = 0;
  int found_rightline_top = 0;
  int found_rightline_bottom = 0;

  int leftred,rightred;
  int testy;
  int point1;
  int point3;
  int point4;
  int point5;
  int point6;
  int point9;
  int x,y;
#define MAXCODE 80
  PyObject *item;
  PyObject *list;
  /*start 1" in and .3" down, looking over 1" for consistent dark */
  point9 = (9*dpi)/10;
  point6 = (6*dpi)/10;
  point5 = dpi/2;
  point4 = (4*dpi)/10;
  point3 = (3*dpi)/10;
  point1 = (dpi/10);
    
#define VERBOSE 1
#ifdef VERBOSE
  printf("DPI %d\n",dpi);
#endif
  for (y=point3;y<dpi;y++) {
    leftred = 0;
    rightred = 0; 
    for (x=dpi;x<(2*dpi);x++){
      p = (UINT8*) &im->image32[y][x];
      leftred += p[0];
    }
    for (x=(im->xsize - (2*dpi));x<(im->xsize - dpi);x++){
      p = (UINT8*) &im->image32[y][x];
      rightred += p[0];
    }
    if (((leftred/dpi) < 112) && (found_topline_left == 0)){
      found_topline_left = y;
    }
    if (((rightred/dpi) < 112) && (found_topline_right == 0)){
      found_topline_right = y;
    }
    if ((found_topline_left > 0) && (found_topline_right > 0)){
      break;
    }
  }
  if ((found_topline_left == 0) || (found_topline_right == 0)){
    Py_INCREF(Py_None);
    return Py_None;
    }
#ifdef VERBOSE
  printf("Past first loop with y values %d %d\n",found_topline_left,found_topline_right);
#endif
  /* look for bottom line on left and right, 1" to 1.3" in from horiz edges, 
     starting 0.3" in from vertical edges
     changed to 0.3" from 1" and 128 intensity from 112 11/24/10 mjt
  */
  for (y = (im->ysize - point3) ; y > (im->ysize - (4*dpi)) ; y--) {
    leftred = 0;
    rightred = 0;
    for (x=dpi;x<(dpi+point3);x++){
      p = (UINT8*) &im->image32[y][x];
      leftred += p[0];
    }
    for (x=(im->xsize - (dpi+point3));x<(im->xsize - dpi);x++){
      p = (UINT8*) &im->image32[y][x];
      rightred += p[0];
    }
    if (((leftred/point3) < 128) && (found_bottomline_left == 0)){
      found_bottomline_left = y;
    }
    if (((rightred/point3) < 128) && (found_bottomline_right == 0)){
      found_bottomline_right = y;
    }
    if ((found_bottomline_left > 0) && (found_bottomline_right > 0)){
      break;
    }
  }
  if ((found_bottomline_left == 0) || (found_bottomline_right == 0)){
    Py_INCREF(Py_None);
      return Py_None;
    }
#ifdef VERBOSE
  printf("Past second loop with y values %d %d\n",
	 found_bottomline_left,
	 found_bottomline_right);
#endif
  /* we should now have the y offsets of the top and bottom lines,
     on both sides.  We should be able to find a solid inch of vertical
     black line joining with our horizontal lines, establishing the 
     equivalent x offsets of the box */
  /* alternatively, we should be able to walk those lines until we
     find a white pixel, allowing for the line to tilt slightly;
     Starting at discovered y and center of tested x zone, x-- and
     check intensity of new point.  If new point is dark, continue.
     If new point is light enough to not be line, check point above 
     and below.  If either is dark enough to be line, adjust y and 
     continue.  Else, declare x to be the left edge of the line.  

*/
  testy = found_topline_left;
  for (x=(3*dpi/2);x>dpi/4;x--){
    p = (UINT8*)&im->image32[testy][x];
    if (p[0]<200) continue;
    p = (UINT8*)&im->image32[testy-1][x];
    if (p[0]<200) {
      testy--;
      continue;
    }
    p = (UINT8*)&im->image32[testy+1][x];
    if (p[0]<200) {
      testy++;
      continue;
    }
    found_leftline_top = x+1;
    break;
  }

  testy = found_topline_right;
  for (x=im->xsize-(3*dpi/2);x>=(im->xsize-(dpi/4));x++){
    p = (UINT8*)&im->image32[testy][x];
    if (p[0]<200) continue;
    p = (UINT8*)&im->image32[testy-1][x];
    if (p[0]<200) {
      testy--;
      continue;
    }
    p = (UINT8*)&im->image32[testy+1][x];
    if (p[0]<200) {
      testy++;
      continue;
    }
    found_rightline_top = x-1;
    break;
  }

  testy = found_bottomline_left;
  for (x=(3*dpi/2);x>dpi/4;x--){
    p = (UINT8*)&im->image32[testy][x];
    if (p[0]<200) continue;
    p = (UINT8*)&im->image32[testy-1][x];
    if (p[0]<200) {
      testy--;
      continue;
    }
    p = (UINT8*)&im->image32[testy+1][x];
    if (p[0]<200) {
      testy++;
      continue;
    }
    found_leftline_bottom = x+1;
    break;
  }

  testy = found_bottomline_right;
  for (x=im->xsize-(3*dpi/2);x>=(im->xsize-(dpi/4));x++){
    p = (UINT8*)&im->image32[testy][x];
    if (p[0]<200) continue;
    p = (UINT8*)&im->image32[testy-1][x];
    if (p[0]<200) {
      testy--;
      continue;
    }
    p = (UINT8*)&im->image32[testy+1][x];
    if (p[0]<200) {
      testy++;
      continue;
    }
    found_rightline_bottom = x-1;
    break;
  }

#ifdef NOTDEF
  for (x=point5;x<dpi;x++) {
    topred = 0;
    bottomred = 0;
    for (y=found_topline_left ; y<(found_topline_left+point3) ; y++){
      p = (UINT8*) &im->image32[y][x];
      p2 = (UINT8*) &im->image32[y][x-(dpi/30)];
      if (p2[0]>200){
	topred += p[0];
      }
      else {
	topred += 255;
      }
    }
    for (y=found_bottomline_left ; y>(found_bottomline_left-point3) ; y--){
      p = (UINT8*) &im->image32[y][x];
      p2 = (UINT8*) &im->image32[y][x-(dpi/30)];
      if (p2[0]>200){
	bottomred += p[0];
      }
      else {
	bottomred += 255;
      }
    }
    // needs to be very dark to avoid confusing with bar code
    //changed threshold from 48 to 96 mjt 6/13/10 
    // changed threshold to 112, adding check for nearby white mjt 11/21/10
    if (((topred/dpi) < point3) && (found_leftline_top == 0)){
#ifdef VERBOSE
      printf("Found leftline top at %d\n",x);
#endif
      found_leftline_top = x;
    }
    if (((bottomred/dpi) < point3) && (found_leftline_bottom == 0)){
#ifdef VERBOSE
      printf("Found leftline bottom at %d\n",x);
#endif
      found_leftline_bottom = x;
    }
    if ((found_leftline_top > 0) && (found_leftline_bottom > 0)){
      break;
    }
  }
  if ((found_leftline_top == 0) || (found_leftline_bottom == 0)){
    Py_INCREF(Py_None);
    return Py_None;
  }
#ifdef VERBOSE
  printf("Past third loop with x values %d %d\n",
	 found_leftline_top,
	 found_leftline_bottom);
#endif

  for (x=im->xsize - point3 ; x > im->xsize - dpi ; x--) {
#ifdef VERBOSE
#endif
    topred = 0;
    bottomred = 0;
    
    // reduce size of check zone from dpi to point3 0.3" mjt 11/24/2010
    for (y=found_topline_right ; y<(found_topline_right+point3) ; y++){
      p = (UINT8*) &im->image32[y][x];
      p2 = (UINT8*) &im->image32[y][x+(dpi/30)];
      if (p2[0] > 200){
	topred += p[0];
      }
      else {
	topred += 255;
      }
#ifdef VERBOSE
#endif
    }
    for (y=found_bottomline_right ; y>(found_bottomline_right-point3) ; y--){
      p = (UINT8*) &im->image32[y][x];
      p2 = (UINT8*) &im->image32[y][x+(dpi/30)];
      // add the pixel's red value, 
      // only if the pixel 1/30" to the right is white;
      // otherwise, treat pixel as white.
      // This loses bar code but pixs up vline.
      if (p2[0] > 200){
	bottomred += p[0];
      }
      else {
	bottomred += 255;
      }
    }
#ifdef VERBOSE
    printf("x %d Topred %d bottomred %d\n",x,topred/point3,bottomred/point3);
#endif
    if (((topred/point3) < 112) && (found_rightline_top == 0)){
      found_rightline_top = x;
    }
    if (((bottomred/point3) < 112) && (found_rightline_bottom == 0)){
      found_rightline_bottom = x;
    }
    if ((found_rightline_top > 0) && (found_rightline_bottom > 0)){
      break;
    }
  }
#ifdef VERBOSE
  printf("Topred %d bottomred %d dpi %d\n",topred,bottomred,dpi);
  printf("Found_rightline_top %d\n",found_rightline_top);
  printf("Found_rightline_bottom %d\n",found_rightline_bottom);
#endif
  if ((found_rightline_top == 0) || (found_rightline_bottom == 0)){
    Py_INCREF(Py_None);
    return Py_None;
  }
#ifdef VERBOSE
  printf("Past fourth loop with x values %d %d\n",
	 found_rightline_top,
	 found_rightline_bottom);
#endif

#endif

  /* now return a list of the four (x,y) pairs you've accumulated,
     starting at ULC and going clockwise */
  list = PyList_New(0);
  item = Py_BuildValue("(ii)", found_leftline_top,found_topline_left);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list, item);
  item = Py_BuildValue("(ii)", found_rightline_top,found_topline_right);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list, item);
  item = Py_BuildValue("(ii)", found_rightline_bottom,found_bottomline_right);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list, item);
  item = Py_BuildValue("(ii)", found_leftline_bottom,found_bottomline_left);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list, item);
  return list;
}

/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject*
getdieboldlandmarks(Imaging im, int dpi, int need_vops)
{
  UINT8 *p;
  int ulc[2];
  int urc[2];
  int lrc[2];
  int llc[2];
  int point3;
  int x,y;
  int xcontig = 0;
  int ycontig = 0;
  PyObject *item;
  PyObject *list;

  point3 = (3*dpi)/10;
    
  // for the Diebold landmarks, look for the inside upper corners
  // of the first and last dashes at the top and bottom; 
  // a Diebold dash is a solid black zone at least 1/20 * dpi tall
  // and 1/16" wide (possibly clipped at edge, full dash is 1/6")
  // beginning between 0.3" and 1.0" from the top of the ballot,
  // turning white somewhere within the first 1/2 * dpi, 
  // and REPEATED above or below (to protect against misreading
  // highly tilted ballots)


#ifdef VERBOSE
  printf("DPI %d\n",dpi);
#endif
  ulc[0] = 0;
  ulc[1] = 0;
  ycontig = 0;
  for (y=point3;y<dpi;y++) {
    xcontig = 0;
    for (x=0;x<(dpi/2);x++){
      p = (UINT8*) &im->image32[y][x];
      if (*p < 128){
	xcontig++;
      }
      else if (xcontig >= (dpi/16)){
	ycontig++;
	break;
      }
      else {
	xcontig = 0;
      }
    }
    if (ycontig >= (dpi/20)){
      ulc[0] = x;
      ulc[1] = y - ycontig;
      break;
    }
  }
  ycontig = 0;
  printf("Search for urc.\n");
  for (y=point3;y<dpi;y++) {
    xcontig = 0;
    for (x=im->xsize-1;x>(im->xsize-(dpi/2));x--){
      p = (UINT8*) &im->image32[y][x];
      if (*p < 128){
	xcontig++;
      }
      else if (xcontig >= (dpi/16)){
	ycontig++;
	break;
      }
      else {
	xcontig = 0;
      }
    }
    if (ycontig > 1){
      printf("ycontig=%d,x=%d\n",ycontig,x);
    }
    if (ycontig >= (dpi/20)){
      urc[0] = x;
      urc[1] = y - ycontig;
      break;
    }
  }
  ycontig = 0;
  for (y=im->ysize - 1; y > (im->ysize-dpi); y--) {
    xcontig = 0;
    for (x=im->xsize-1;x>(im->xsize-(dpi/2));x--){
      p = (UINT8*) &im->image32[y][x];
      if (*p < 128){
	xcontig++;
      }
      else if (xcontig >= (dpi/16)){
	ycontig++;
	break;
      }
      else {
	xcontig = 0;
      }
    }
    if (ycontig >= (dpi/20)){
      lrc[0] = x;
      lrc[1] = y + ycontig;
      break;
    }
  }
  ycontig = 0;
  for (y=im->ysize - 1; y > (im->ysize-dpi); y--) {
    xcontig = 0;
    for (x=0;x<(dpi/2);x++){
      p = (UINT8*) &im->image32[y][x];
      if (*p < 128){
	xcontig++;
      }
      else if (xcontig >= (dpi/16)){
	ycontig++;
	break;
      }
      else {
	xcontig = 0;
      }
    }
    if (ycontig >= (dpi/20)){
      llc[0] = x;
      llc[1] = y + ycontig;
      break;
    }
  }
  /* now return a list of the four (x,y) pairs you've accumulated,
     starting at ULC and going clockwise */
  list = PyList_New(0);//!!!
  item = Py_BuildValue("[ii]", ulc[0],ulc[1]);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list,item);
  item = Py_BuildValue("[ii]", urc[0],urc[1]);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list,item);
  item = Py_BuildValue("[ii]", lrc[0],lrc[1]);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list,item);
  item = Py_BuildValue("[ii]", llc[0],llc[1]);
  if (!item){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list,item);
  return (list);
}

/* BALLOT ANALYSIS (works with RGB only) */
/* highly specific to a given size, perhaps add size as parameters */
static  int test_for_oval(Imaging im, int dpi, int x,int y, int contig)
{
  int x2;
  int retval = 0;
  int qualify = 0;
  int disqualify = 0;
  UINT8 *p2, *p3, *p4, *p5;
  /* disqualify if it is not completely white 
     for surrounding 1/8" on line 1/20" below */
#ifdef VERBOSE
  printf("Testing for oval at (%d,%d)\n",x,y);
#endif
  for (x2 = x-(dpi/16);x2<(x+(dpi/16));x2++){
    p2 = (UINT8 *) &im->image32[y+(dpi/20)][x2];
    p3 = (UINT8 *) &im->image32[y+1+(dpi/20)][x2];
    p4 = (UINT8 *) &im->image32[y-1+(dpi/20)][x2];
    if ((*p2 < 224)||(*p3 < 224)||(*p4 < 224)){
      disqualify++;
    }
    if (disqualify > 1){
      return(0);
    }
  }
  /* disqualify if it is not completely white
     for surrounding 1/8" on top row 1/6" before or after */
  disqualify = 0;
  for (x2 = x-(dpi/16);x2<x;x2++){
    p2 = (UINT8 *) &im->image32[y][x2 - (dpi/6)];
    if (*p2 < 224){
      disqualify++;
    }
    if (disqualify > 1){
      return(0);
    }
  }
  disqualify = 0;
  for (x2 = x;x2<(x+(dpi/16));x2++){
    p2 = (UINT8 *) &im->image32[y][x2 + (dpi/6)];
    if (*p2 < 224){
      disqualify++;
    }
    if (disqualify > 1){
      return(0);
    }
  }
  // and nearby values of y
  for (x2 = x+((3*dpi)/16);x2<(x+(dpi/4));x2++){
    p2 = (UINT8 *) &im->image32[y+(dpi/16)][x2];
    p3 = (UINT8 *) &im->image32[y+(dpi/24)][x2];
    p4 = (UINT8 *) &im->image32[y+(dpi/12)][x2];
    if (*p2 < 224){
      disqualify++;
    }
    if (*p3 < 224){
      disqualify++;
    }
    if (*p4 < 224){
      disqualify++;
    }
    if (disqualify > 1){
      return(0);
    }
  }
  /* consider it an oval if not disqualified
     and dark pixels 1/10" below 
     and dark pixels at 1/8" back and 1/20" below */
  for (x2 = x-contig-2 ;x2 < (x+2);x2++){
    p3 = (UINT8 *) &im->image32[y+(dpi/10)-1][x2];
    p4 = (UINT8 *) &im->image32[y+(dpi/10)][x2];
    p5 = (UINT8 *) &im->image32[y+(dpi/10)+1][x2];
    /* we want to find darkness here */
    if ((*p3 < 192)||(*p4 < 192)||(*p5<192)){
      qualify++;
      //	     *p2, *p3,*p4,*p5);
    }
    if (qualify > 2)break;
  }
  /* you want to encounter at least another black pixel
     near the extreme left and right of the oval to be certain */
  for (x2 = x-(dpi/16);x2<(x+(dpi/16));x2++){
    p2 = (UINT8 *) &im->image32[y+(dpi/20)][x2 - (dpi/8)];
    p3 = (UINT8 *) &im->image32[y+1+(dpi/20)][x2 - (dpi/8)];
    if (*p2 < 128){
      qualify++;
    }
    if (*p3 < 128){
      qualify++;
    }
    if (qualify > 4) break;
  }
#ifdef VERBOSE
  if (qualify > 4){
    printf("Checking from (%d,%d) to (%d,%d)\n",x,y+(dpi/16),x,y+((3*dpi)/16));
  }
#endif
  for (x2 = x-(dpi/16);x2<(x+(dpi/16));x2++){
    p2 = (UINT8 *) &im->image32[y+(dpi/20)][x2 + (dpi/8)];
    p3 = (UINT8 *) &im->image32[y+1+(dpi/20)][x2 + (dpi/8)];
    if (*p2 < 128){
      qualify++;
    }
    if (*p3 < 128){
      qualify++;
    }
    if (qualify > 6) break;
  }
  if (qualify > 6) {
    retval = 1;
  }
  return retval;
}
/* BALLOT ANALYSIS (works with RGB only) */
/* return 0 for unknown, 1 for ESS, 2 for Diebold, NYI: 3 for Hart */
static inline PyObject*
getballotbrand(Imaging im, int dpi)
{
#define MAXREPS 9
  int darklength[2][MAXREPS];
  int lightlength[2][MAXREPS];
  int lengthcount[2];
  int starty;
  int endy;
  int startx;
  int endx;
  int x,y;
  int n,m;
  UINT8 *p;
  int this_lightqq[2];
  int last_lightqq[2];
  int accum[2];
  int equals[2];
  int one2three[2];
  int sixths[2];
  int sixteenths[2];
  int retval = 0;
  int twentyfifth;
  /* return 1 if ESS, 2 if Diebold, NYI:3 if Hart, 0 if unsure */
  twentyfifth = dpi/25;
  /* start with zero'd arrays */
  for (n=0;n<2;n++){
    for (m=0;m<MAXREPS;m++){
      darklength[n][m] = 0;
      lightlength[n][m] = 0;
    }
    this_lightqq[n] = 0;
    last_lightqq[n] = 1;
    accum[n] = 0;
    lengthcount[n] = 0;
    equals[n] = 0;
    one2three[n] = 0;
    sixths[n] = 0;
    sixteenths[n] = 0;
  }
  /* search halfway down the leftmost half inch, then the rightmost, 
     looking over two vertical inches for dark white repetitions */
  starty = im->ysize/2;
  endy = starty+(2*dpi);
  startx = 0;
  endx = dpi/3;
  accum[0] = 0;
  accum[1] = 0;
  for (n=0;n<2;n++){
#ifdef VERBOSE
    printf("In getballotbrand for loop n = %d\n",n);
#endif
    /* we start in light mode */
    last_lightqq[n] = 1;
    for (y = starty; y <= endy; y++){
      /* accumulate x values on this line's left during first pass */
#ifdef VERBOSE
      printf("In getballotbrand for loop n = %d, y = %d\n",n,y);
#endif
      if (n==0){
	for (x = startx; x <= endx; x++){
	  p = (UINT8*) &im->image32[y][x];
	  accum[n] += p[0];
	}
      }
      /* and on this line's right during second pass */
      else {
	for (x = im->xsize-1; x >= im->xsize-(dpi/3); x--){
	  /* accumulate x values on this line */
	  p = (UINT8*) &im->image32[y][x];
	  accum[n] += p[0];
	}
      }
      /* and divide by x count to get avg */
      accum[n] /= (dpi/3);
#ifdef VERBOSE
      if (n==0){
	printf("y=%d accum[n]=%d\n",y,accum[n]);
      }
#endif
      /* we may not be entirely in the dash stripe, */
      /* so reasonable darkness counts as dark */
      if (accum[n] > 224){
	this_lightqq[n] = 1;
      }
      else {
	this_lightqq[n] = 0;
      }
      if (this_lightqq[n] && last_lightqq[n]){
	/* this is an additional light line */
	lightlength[n][lengthcount[n]]++;
      }
      if ((! this_lightqq[n]) && (! last_lightqq[n])){
	/* this is an additional dark line */
	darklength[n][lengthcount[n]]++;
      }
      if (this_lightqq[n] && (! last_lightqq[n])){
	/* this is a new light line, increment the lengthcount variable */
	lengthcount[n]++;
	if (lengthcount[n]>=MAXREPS){
	  printf("Breaking out of for y due to excess lengthcount\n");
	  break;
	}
	lightlength[n][lengthcount[n]] = 1;
      }
      if ((! this_lightqq[n]) && last_lightqq[n]){
	/* this is a new dark line */
	darklength[n][lengthcount[n]] = 1;
      }
      last_lightqq[n] = this_lightqq[n];
    }/* end of for y */
  } /* end of for n */
  /* we now have light and dark lengths over the two inches */
  /* of left and right edges */
  /* if it's an ESS, dark and light after the first should be roughly equal */
  for (n=0;n<2;n++){
    for (m=1;m<=lengthcount[n];m++){
#ifdef VERBOSE      
      printf("left %d rep %d dark %d light %d\n",
	     n,
	     m,
	     lightlength[n][m],
	     darklength[n][m]);
#endif
      if (abs(lightlength[n][m]-darklength[n][m])<twentyfifth) {
	equals[n]++;
      }
      if (abs(lightlength[n][m]-(dpi/6))<twentyfifth) {
	sixths[n]++;
      }
      if (abs(darklength[n][m]-(dpi/6))<twentyfifth) {
	sixths[n]++;
      }
      if (abs(lightlength[n][m] - (3*darklength[n][m]))<twentyfifth) {
	one2three[n]++;
      }
      if (abs(darklength[n][m]-(dpi/16))<twentyfifth) {
	sixteenths[n]++;
      }
      if (abs(lightlength[n][m]-((3*dpi)/16))<twentyfifth) {
	sixteenths[n]++;
      }
    }
    if (lengthcount[n] < 3){
      /* this cannot be identified, may be Hart */
      retval = 0;
    }
    if ((equals[n] >= (lengthcount[n]-2)) && (sixths[n] >= (lengthcount[n]-2))){
      /* this is an ESS */
      retval = 1;
      break;
    }
    if ((one2three[n] >= (lengthcount[n]-2)) && (sixteenths[n] >= (lengthcount[n] - 2))){
      /* this is a Diebold */
      retval = 2;
      break;
    }
    /* if something has been identified from the left, no need to look right */
    if (retval > 0) {
      break;
    }
  } /* for n = 0 */
  return (Py_BuildValue("i", retval));
}


/* BALLOT ANALYSIS (works with RGB only) */
/*"""
Return a list of the blocktype, x, y and, linediff and xdiff.
"""*/
static inline PyObject*
getesstilt(Imaging im, int dpi)
{
  UINT8 *p;
  int leftred,rightred;
  int point1;
  int point3;
  int point4;
  int point5;
  int point6;
  int point9;
  int blocktype = 0;
  int blockx = 0;
  int blocky = 0;
  int x,y;
  int thirtysecond;
# define MAXDZ 10
  int counter;
  int ydiff = 0;
  int linediff1=0;
  int linecount[5];
  int n;
  /*start 0.1" in and .4" down, looking over 1/2" square for black block */
  point9 = (9*dpi)/10;
  point6 = (6*dpi)/10;
  point5 = dpi/2;
  point4 = (4*dpi)/10;
  point3 = (3*dpi)/10;
  point1 = (dpi/10);
  thirtysecond = (dpi/32);
  ydiff = 2*dpi - (dpi/15);
  for (n=0;n<5;n++)
    linecount[n] = 0;
  for (y=point4;y<dpi;y++) {
    leftred = 0;
    rightred = 0;
    
    for (x=point1;x<dpi;x++){
      p = (UINT8*) &im->image32[y][x];
      leftred += p[0];
    }
    for (x=im->xsize - point6;x<im->xsize - point1;x++){
      p = (UINT8*) &im->image32[y][x];
      rightred += p[0];
    }
    if ((rightred/point5) < 64){
      /* it's a long block on the right, an upside down front */
      blocktype = 3;
      linecount[3]++;
    }
    else if ((rightred/point5) < 224){
      /* it's a short block on the right, a back */
      blocktype = 4;
      linecount[4]++;
    }
    else if ((leftred/point9) < 128){
      /* it's a long block on the left, a front*/
      blocktype = 2;
      linecount[2]++;
    }
    else if ((leftred/point9) < 224){
      /* it's a short block on the left, an upside down back */
      blocktype = 1;
      linecount[1]++;
    }
    else {
      /* it's too light to be a block at all */
    }
#ifdef VERBOSE
    if (blocktype > 0){

      printf("Blocktype %d y %d linecounts %d %d %d %d %d\n",blocktype,y,
	     linecount[0],
	     linecount[1],
	     linecount[2],
	     linecount[3],
	     linecount[4]);

    }
#endif
    if ((blocktype > 0) && (linecount[blocktype] > (dpi/8))){
      /* save y offset at which block starts */
      blocky = y-linecount[blocktype];
      break;
    }
  }

#ifdef VERBOSE
  printf("blocktype %d\n",blocktype);
#endif
  // printf("WARNING: if left above right by more than 1/8", 
  // left blocks will take priority.\n");
  if (blocktype == 1 || blocktype==3) {
    /* upside down back */
    return Py_BuildValue("iiiii", blocktype,blockx,blocky,0,1);
  }

  /* Upside down ballot images have bailed. */

  /* find the x offset of the block */
  /* Fronts, 2, have blocks on left */
  
  if (blocktype == 2){
    for (x=point1;x<dpi;x++){
      p = (UINT8*) &im->image32[blocky+thirtysecond][x];
      if (*p < 128){
	if ((*(p+1) < 128) 
	    &&(*(p+2) < 128) ){
	}
	blockx = x;
	break;
      }
    }
  }
  /* Backs, 4, have blocks on right */
  else if (blocktype == 4){
    for (x = (im->xsize - point6);
	 x < (im->xsize-point3);
	 x++){
      p = (UINT8*) &im->image32[blocky+thirtysecond][x];
#ifdef VERBOSE
      printf("x %d y %d p %d\n",x,blocky+thirtysecond,*p);
#endif
      if (*p < 128){
	if ((*(p+1) < 128) 
	    &&(*(p+2) < 128) ){
	}
	blockx = x;
	break;
      }
    }
  }
  else{
    return Py_BuildValue("iiiii",0,blockx,blocky,0,1);
  }

  /* Bail if you can't find the block. */
  if ((blockx==0) || (blocky==0)){
    return Py_BuildValue("iiiii",0,blockx,blocky,0,1);
  }

  /* you now have the starting (x,y) for the block */
  /* and know you are looking at a right side up front (blocktype 2) */
  /* or a right side up back (blocktype 4) */
  
  /* if you are looking at a front, */
  /* first find out how much of a tilt there is, */
  /* by seeing how the starting x of the blocks changes as you go down */
  counter = 0;
  if (blocktype == 2)
  { 
    UINT8 *p1, *p2;
    int p1x, p2x, p1_contig, p2_contig;
    p1_contig = 0;
    p2_contig = 0;
    p1x = 0;
    p2x = 0;
    for(x=blockx -(dpi/10); x < blockx + (dpi/5); x++){
      p1 = (UINT8*) &im->image32[blocky+point1][x];
      /* second test point is down 2" less 1/15" from the first */
      p2 = (UINT8*) &im->image32[blocky+ydiff][x];
      if (*p1 < 64){
	p1_contig++;
	if ((p1x == 0) && (p1_contig > (dpi/20))){
	  p1x = x;
	}
      }
      else {
	p1_contig = 0;
      }
      if (*p2 < 64){
	p2_contig++;
	if ((p2x == 0) && (p2_contig > (dpi/20))){
	  p2x = x;
	}
      }
      else {
	p2_contig = 0;
      }
      if ((p1x > 0) && (p2x > 0))break;
    }
#ifdef VERBOSE
    printf ("blocktype %d p1x %d p2x %d\n",blocktype, p1x,p2x);
#endif
    linediff1 = p2x - p1x;
  }
  /* if you are looking at a back, try the same, but using different x's */
  if (blocktype == 4)
  { 
    UINT8 *p1, *p2;
    int p1x, p2x, p1_contig, p2_contig;
    p1_contig = 0;
    p2_contig = 0;
    p1x = 0;
    p2x = 0;
    for(x=blockx -(dpi/10); x < blockx + (dpi/5); x++){
      p1 = (UINT8*) &im->image32[blocky+point1][x];
      /* second test point is down 2" less 1/15" from the first */
      p2 = (UINT8*) &im->image32[blocky+ydiff][x];
      if (*p1 < 64){
	p1_contig++;
	if ((p1x == 0) && (p1_contig > (dpi/20))){
	  p1x = x;
	}
      }
      else {
	p1_contig = 0;
      }
      if (*p2 < 64){
	p2_contig++;
	if ((p2x == 0) && (p2_contig > (dpi/20))){
	  p2x = x;
	}
      }
      else {
	p2_contig = 0;
      }
      if ((p1x > 0) && (p2x > 0))break;
    }
#ifdef VERBOSE
    printf ("blocktype %d p1x %d p2x %d\n",blocktype, p1x,p2x);
#endif
    linediff1 = p2x - p1x;
  }
  return Py_BuildValue("iiiii",blocktype,blockx,blocky,linediff1,ydiff);
  
}

/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject*
getessheadersandcodes(Imaging im, int dpi, int blocktype, int blockx, int blocky, int linediff, int ydiff)
{
  UINT8 *p;
  int point1;
  int point4;
  int point5;
  int point6;
  int point9;
  int contig = 0;
  int x2=0;
  int x,y;
  int yadj = 0;
# define MAXDZ 10
  int darkzone_start[MAXDZ];
  int darkzone_end[MAXDZ];
  int darkzone_count = 0;
  int counter;
  int startx;
#define MAXCODE 80
  int code[MAXCODE];
  int codecount = 0;
  int image_inches;
  PyObject *item;
  PyObject *codelist;
  PyObject *columnlist;
  PyObject *retlist;

  point9 = (9*dpi)/10;
  point6 = (6*dpi)/10;
  point5 = dpi/2;
  point4 = (4*dpi)/10;
  point1 = (dpi/10);
  /* adjusting for acceptable tilt */
  /* scan a line halfway down into the header row (1/12") */
  /* to find vote column offsets */
  /* which will be > 1/5" of contiguous black pixels */
  y=blocky+(dpi/12);
  darkzone_count = 0;
  if (blocktype == 2)startx = dpi;
  else startx = dpi/2;
		       
  for (x = startx ; 
       x < (im->xsize - dpi) ; 
       x++) {
    if (blocktype==2){
      yadj = (int)(-(linediff * (x/(ydiff+0.01))));
    }
    if (blocktype==4){
      yadj = (int)((linediff *((blockx-x)/(ydiff+0.01))));
    }
    p = (UINT8*) &im->image32[y+yadj][x];
    //if (x > 1100)printf("x %d im->xsize %d dpi %d\n",x,im->xsize,dpi);
    if (*p < 128){
      UINT8 *p2, *p3, *p4;
      p2 = (UINT8*) &im->image32[y+yadj][x+1];
      p3 = (UINT8*) &im->image32[y+yadj][x+2];
      p4 = (UINT8*) &im->image32[y+yadj][x+3];
      if ((*p2 < 128) && (*p3 < 128) && (*p4 < 128)){
	/* four dark pixels? Worth checking to see if you have 1/5" */
	x2 = x;
	contig = 1;
	do {
	  p = (UINT8 *)&im->image32[y+yadj][x2++];
	  contig++;
	} while(*p < 128 && contig <= (dpi/5));
	if (contig > (dpi/5)){
	  darkzone_start[darkzone_count] = x;
	  /* note that the actual zone width is 1/4" */
	  darkzone_end[darkzone_count] = x+(dpi/4);
	  darkzone_count++;
#ifdef VERBOSE
	  printf("Contig %d start %d end %d, count %d\n",contig,x,x+contig,darkzone_count);
#endif
	  if (darkzone_count >= MAXDZ){
	    /* something's gone wrong */
	    Py_INCREF(Py_None);
	    return Py_None;
	  }
	  x += contig;
	}
      }
    }
  }
#ifdef VERBOSE
  printf("Darkzone count %d\n",darkzone_count);
  for(counter=0;counter<darkzone_count;counter++){
    printf("Counter %d darkzone %d to %d\n",
	   counter,
	   darkzone_start[counter],
	   darkzone_end[counter]
	   );
  }
#endif
  /* first row is 2/3" from top, bottom row is 2/3" from bottom at 14" */
  /* so to get from first row to bottom row, add 14" less 4/3" = 12 2/3" */
  /* determine image size in inches, based on dpi and im->ysize */
  image_inches = (int)((im->ysize/dpi)+0.5);
  /* adds height less 4/3 inches */
  //y += (((image_inches-2)*dpi)+(2*(dpi/3)));
  /* or force to bottom less half inch less twelfth... */

  y = im->ysize - (dpi/2) - (dpi/12);
#ifdef VERBOSE
  printf("Looking for darkzones at y adjusted from %d via linediff1 %d\n",y,linediff);
#endif
  for (x= startx  ; 
       x < (im->xsize - dpi) ; x++) {
    if (blocktype==2){
      yadj = (int)(-(linediff * (x/(ydiff+0.01))));
    }
    if (blocktype==4){
      yadj = (int)((linediff *((blockx-x)/(ydiff+0.01))));
    }
    
    p = (UINT8*) &im->image32[y+yadj][x];
    if (*p < 128){
      if (1){
	/* (*(p+1) < 128)  &&(*(p+2) < 128) 
	   && (*(p+3) < 128)  && (*(p+4) < 128) ){*/
	/* five dark pixels? Worth checking to see if you have 1/5" */
	x2 = x;
	contig = 1;
	do {
	  p = (UINT8 *)&im->image32[y+yadj][x2++];
	  contig++;
	} while(*p < 128);
	if (contig > (dpi/5)){
	  darkzone_start[darkzone_count] = x;
	  /* note that the actual zone length is 1/4" */
	  darkzone_end[darkzone_count] = x+(dpi/4);
	  darkzone_count++;
	  if (darkzone_count >= MAXDZ){
	    /* something's gone wrong */
	    Py_INCREF(Py_None);
	    return Py_None;
	  }
	  x += contig;
	}
      }
    }
  }
#ifdef VERBOSE
  printf("Darkzone count %d\n",darkzone_count);
  for(counter=0;counter<darkzone_count;counter++){
    printf("Counter %d darkzone %d to %d\n",
	   counter,
	   darkzone_start[counter],
	   darkzone_end[counter]
	   );
  }
#endif


  if (blocktype == 4) {
    code[0] = 192;
    codecount = 1;
  }
  else if (blocktype == 2) {
  /* using the 3 blocks per inch to remain in sync, and using the linediff */
  /* to determine tilt or skew, extract the */
  /* code created by the presence or absence of blocks in the second column */
    int x1, x2 ,y, x, darkwidth;
    int contig0 = 0;
    int blockcount = 0;
    int adjustper6 = linediff;
    x1 = blockx + (dpi/2);
    x2 = blockx + (3*dpi/4);
    x = x1 + (x2-x1)/2;
    contig0 = 0;
    for (y = blocky + point6; y < (im->ysize - dpi); y+= (dpi/3)){
      UINT8 *p2;
      darkwidth = 0;
      blockcount++;
      /* try accomodating tilt by backing off by 2" of tilt every 6/3" */
      /* we may !!! want to confirm this by comparing top and bottom   */
      /* "column" x offsets */
      if ((blockcount%6)==0){
#ifdef VERBOSE
	printf("Adj x1 from %d to %d at y = %d\n",x1,x1+adjustper6,y);
	printf("Adj x2 from %d to %d at y = %d\n",x2,x2+adjustper6,y);
#endif
	x1 += adjustper6;
	x2 += adjustper6;
      }
      for (x = x1;x < x2; x+=(dpi/30)){
	p2 = (UINT8 *) &im->image32[y][x];
	if (*p2 < 64){
	  darkwidth++;
	}
      }
      if (darkwidth == 0){
	contig0++;
      }
      else if (darkwidth <= 5){
	/* handle any contig0 */
	code[codecount] = contig0;
	codecount++;
	contig0 = 0;
	code[codecount] = 64;
	codecount++;
      }
      else if (darkwidth <= 10){
	/* handle any contig0 */
	code[codecount] = contig0;
	codecount++;
	contig0 = 0;
	code[codecount] = 128;
	codecount++;
      }
    }
    code[codecount] = contig0;
    codecount++;
#ifdef VERBOSE
    for (counter = 0;counter<codecount;counter++)printf("%d ",code[counter]);
#endif
  }
#ifdef VERBOSE
  printf("\nCodecount %d\n",codecount);
#endif
  /* build return values !!!*/
  codelist = PyList_New(0);
  columnlist = PyList_New(0);
  retlist = PyList_New(0);
  for (counter=0;counter<codecount;counter++){
    item = Py_BuildValue("i", code[counter]);
    if (!item){
      Py_DECREF(codelist);
      return NULL;
    }
    PyList_Append(codelist,item);
  }
  for (counter=0;counter<darkzone_count;counter++){
    item = Py_BuildValue("[ii]", darkzone_start[counter],darkzone_end[counter]);
    if (!item){
      Py_DECREF(columnlist);
      return NULL;
    }
    PyList_Append(columnlist,item);
  }
  PyList_Append(retlist,codelist);
  PyList_Append(retlist,columnlist);
  return retlist ;
}  

/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject*
getessheaderscodesovals(Imaging im, int dpi, int blocktype, int blockx, int blocky, int linediff, int ydiff)
{
  UINT8 *p;
  int point1;
  int point4;
  int point5;
  int point6;
  int point9;
  int thirtysecond;
  int contig = 0;
  int yadj = 0;
  int x2=0;
  int x,y;
# define MAXDZ 10
  int darkzone_start[MAXDZ];
  int darkzone_end[MAXDZ];
  int darkzone_count = 0;
  int counter;
  int startx;
#define MAXOVALS 100
  int oval[MAXOVALS*2];
  int ovalcount=0;
#define MAXCODE 80
  int code[MAXCODE];
  int codecount = 0;
  int ycontig = 0;
  int image_inches;
  PyObject *item;
  PyObject *dict;
  PyObject *list;

  point9 = (9*dpi)/10;
  point6 = (6*dpi)/10;
  point5 = dpi/2;
  point4 = (4*dpi)/10;
  point1 = (dpi/10);
  /* adjusting for acceptable tilt */
  /* scan a line halfway down into the header row (1/12") */
  /* to find vote column offsets */
  /* which will be > 1/5" of contiguous black pixels */
  y=blocky+(dpi/12);
  darkzone_count = 0;
  if (blocktype == 2)startx = dpi;
  else startx = dpi/2;
		       
  for (x = startx ; 
       x < (im->xsize - dpi) ; 
       x++) {
    if (blocktype==2){
      yadj = (int)(-(linediff * (x/(ydiff+0.01))));
    }
    if (blocktype==4){
      yadj = (int)((linediff *((blockx-x)/(ydiff+0.01))));
    }
    p = (UINT8*) &im->image32[y+yadj][x];
    //if (x > 1100)printf("x %d im->xsize %d dpi %d\n",x,im->xsize,dpi);
    if (*p < 128){
      UINT8 *p2, *p3, *p4;
      p2 = (UINT8*) &im->image32[y+yadj][x+1];
      p3 = (UINT8*) &im->image32[y+yadj][x+2];
      p4 = (UINT8*) &im->image32[y+yadj][x+3];
      if ((*p2 < 128) && (*p3 < 128) && (*p4 < 128)){
	/* four dark pixels? Worth checking to see if you have 1/5" */
	x2 = x;
	contig = 1;
	do {
	  p = (UINT8 *)&im->image32[y+yadj][x2++];
	  contig++;
	} while(*p < 128 && contig <= (dpi/5));
	if (contig > (dpi/5)){
	  darkzone_start[darkzone_count] = x;
	  /* note that the actual zone width is 1/4" */
	  darkzone_end[darkzone_count] = x+(dpi/4);
	  //darkzone_end[darkzone_count] = x+contig;
	  darkzone_count++;
	  if (darkzone_count >= MAXDZ){
	    /* something's gone wrong */
	    Py_INCREF(Py_None);
	    return Py_None;
	  }
	  x += contig;
	}
      }
    }
  }
#ifdef VERBOSE
  printf("Darkzone count %d\n",darkzone_count);
  for(counter=0;counter<darkzone_count;counter++){
    printf("Counter %d darkzone %d to %d\n",
	   counter,
	   darkzone_start[counter],
	   darkzone_end[counter]
	   );
  }
#endif
  /* first row is 2/3" from top, bottom row is 2/3" from bottom at 14" */
  /* so to get from first row to bottom row, add 14" less 4/3" = 12 2/3" */
  /* determine image size in inches, based on dpi and im->ysize */
  image_inches = (int)((im->ysize/dpi)+0.5);
  /* adds height less 4/3 inches */
  //y += (((image_inches-2)*dpi)+(2*(dpi/3)));
  /* or force to bottom less half inch less twelfth... */
  y = im->ysize - (dpi/2) - (dpi/12);
#ifdef VERBOSE
  printf("Looking for darkzones at y adjusted from %d via linediff1 %d\n",y,linediff);
#endif
  for (x= startx  ; 
       x < (im->xsize - dpi) ; x++) {
    if (blocktype==2){
      yadj = -(linediff * (x/(ydiff+0.01)));
    }
    else if (blocktype==4){
      yadj = (linediff * ((blockx-x)/(ydiff+0.01)));
    }
#ifdef VERBOSE
    if (x==(im->xsize-dpi-1))printf("Ending y %d and yadj %d give %d\n",y,yadj,y+yadj);
#endif
    p = (UINT8*) &im->image32[y+yadj][x];
    if (*p < 128){
      if (1){
	/* (*(p+1) < 128)  &&(*(p+2) < 128) 
	   && (*(p+3) < 128)  && (*(p+4) < 128) ){*/
	/* five dark pixels? Worth checking to see if you have 1/5" */
	x2 = x;
	contig = 1;
	do {
	  p = (UINT8 *)&im->image32[y+yadj][x2++];
	  contig++;
	} while(*p < 128);
	if (contig > (dpi/5)){
	  darkzone_start[darkzone_count] = x;
	  /* note that the actual zone width is 1/4" */
	  darkzone_end[darkzone_count] = x+(dpi/4);
	  darkzone_count++;
	  if (darkzone_count >= MAXDZ){
	    /* something's gone wrong */
	    Py_INCREF(Py_None);
	    return Py_None;
	  }
	  x += contig;
	}
      }
    }
  }
#ifdef VERBOSE
  printf("Darkzone count %d\n",darkzone_count);
  for(counter=0;counter<darkzone_count;counter++){
    printf("Counter %d darkzone %d to %d\n",
	   counter,
	   darkzone_start[counter],
	   darkzone_end[counter]
	   );
  }
#endif

  if (blocktype == 4) {
    code[0] = 192;
    codecount = 1;
  }
  else if (blocktype == 2) {
  /* using the 3 blocks per inch to remain in sync, and using the linediff */
  /* to determine tilt or skew, extract the */
  /* code created by the presence or absence of blocks in the second column */
    int x1, x2 ,y, x, darkwidth;
    int contig0 = 0;
    int blockcount = 0;
    int adjustper6 = linediff;
    x1 = blockx + (dpi/2);
    x2 = blockx + (3*dpi/4);
    x = x1 + (x2-x1)/2;
    contig0 = 0;
    for (y = blocky + point6; y < (im->ysize - dpi); y+= (dpi/3)){
      UINT8 *p2;
      darkwidth = 0;
      blockcount++;
      /* try accomodating tilt by backing off by 2" of tilt every 6/3" */
      /* we may !!! want to confirm this by comparing top and bottom   */
      /* "column" x offsets */
      if ((blockcount%6)==0){
#ifdef VERBOSE
	printf("Adj x1 from %d to %d at y = %d\n",x1,x1+adjustper6,y);
	printf("Adj x2 from %d to %d at y = %d\n",x2,x2+adjustper6,y);
#endif
	x1 += adjustper6;
	x2 += adjustper6;
      }
      for (x = x1;x < x2; x+=(dpi/30)){
	p2 = (UINT8 *) &im->image32[y][x];
	if (*p2 < 64){
	  darkwidth++;
	}
      }
      if (darkwidth == 0){
	contig0++;
      }
      else if (darkwidth <= 5){
	/* handle any contig0 */
	code[codecount] = contig0;
	codecount++;
	contig0 = 0;
	code[codecount] = 64;
	codecount++;
      }
      else if (darkwidth <= 10){
	/* handle any contig0 */
	code[codecount] = contig0;
	codecount++;
	contig0 = 0;
	code[codecount] = 128;
	codecount++;
      }
    }
    code[codecount] = contig0;
    codecount++;
#ifdef VERBOSE
    for (counter = 0;counter<codecount;counter++)printf("%d ",code[counter]);
#endif
  }
#ifdef VERBOSE
  printf("\nCodecount %d\n",codecount);
#endif
  /* now search for at least 1/32" of contiguous dark pixels in each */
  /* of the darkzones, followed by the same zone being light 1/20" below */
  /* and with another set of at least 1/32" of contiguous pixels,    */
  /* approx 1/10" below; this is a vote oval      */
  thirtysecond = dpi/32;
  ovalcount = 0;
  ycontig = 0;
  if (1){
    /* check for completely filled in ovals, if appropriate */
    int xadj = 0;
    for (counter=0;counter<(darkzone_count/2);counter++){
      ycontig = 0;
      for (y=dpi;y<(im->ysize - (dpi/3));y++){
	int suff_contig_at;
	int adjustpertwodpi = linediff;
	contig = 0;
	suff_contig_at = 0;
	/* we must adjust the start and end of x here, as we go down */
	/* adjustment can be */
	if ((y%(2*dpi))==0){
	  xadj += adjustpertwodpi;
	}
	for (x= darkzone_start[counter];x<darkzone_end[counter];x++){
	  p = (UINT8*) &im->image32[y][x+xadj];
	  /* we are looking for black */
	  if (*p < 64){
	    contig++;
	  }
	  else {
	    if (contig >= (dpi/8)){
	      /* row has sufficient contiguous, note x */
	      /* now see if there is at least 1/5" clear */
	      int x2;
	      int passes;
	      UINT8 *p2;
	      passes = 1;
	      for (x2 = x+1;x2<(x+(dpi/5));x2++){
		p2 = (UINT8*) &im->image32[y][x2];
		if (*p2 < 64){
		  passes = 0;
		}
	      }
	      if (passes){
		suff_contig_at = x;
	      }
	      break;
	    }
	    contig = 0;/* !!! */
	  }
	}
	if (suff_contig_at == 0){
	  ycontig=0;
	}
	else {
	  ycontig++;
	  if (ycontig >= (dpi/20)){
	    oval[ovalcount++] = darkzone_start[counter];
	    if (ovalcount>=(MAXOVALS*2)){
	    Py_INCREF(Py_None);
	      return Py_None;
	    }
	    oval[ovalcount++] = y-ycontig;
	    if (ovalcount>=(MAXOVALS*2)){
	    Py_INCREF(Py_None);
	      return Py_None;
	    }
	    y += (dpi/5);
	    ycontig = 0;
	  }
	}
	contig = 0;
      }
    }
    y += (dpi/10);
    if (ovalcount >= (MAXOVALS*2)){
	    Py_INCREF(Py_None);
      return Py_None;
    }
 
    /* check for empty ovals */
    ovalcount = 0;
    for (counter=0;counter<(darkzone_count/2);counter++){
#ifdef VERBOSE
      printf("Column counter %d\n",counter);
#endif
      int xadj = 0;
      for (y=0;y<(im->ysize - (dpi/3));y++){
	contig = 0;
	if (!(y % 128)){
	  xadj = (int)(((float)linediff/ydiff) * y);
	}
	for (x= darkzone_start[counter];x<darkzone_end[counter];x++){
	  p = (UINT8*) &im->image32[y][x+xadj];
	  /* we are looking for dark */
	  if (*p < 240){
	    contig++;
	  }
	  else {
	    if ((contig >= thirtysecond)){
	      if (test_for_oval(im,dpi,x+xadj,y,contig)){
#ifdef VERBOSE
		printf("FOUND OVAL %d ulc at (%d,%d)\n",
		       ovalcount/2,
		       darkzone_start[counter]+xadj,
		       y);
#endif
		oval[ovalcount++] = darkzone_start[counter]+xadj;
		oval[ovalcount++] = y;
		y += (dpi/10);
	      }
	      break;
	    }
	  }
	}
      }
    }
    /* jump to y past the oval */
    y += (dpi/10);
    if (ovalcount >= (MAXOVALS*2)){
      printf("Too many ovals!\n");
	    Py_INCREF(Py_None);
      return Py_None;
    }
  }


  /* create a python list and return: */
  /* block type, block x, block y, number of dark zones, */
  /* darkzonestart, darkzoneend....darkzonestart,darkzoneend */ 
  list = PyList_New(0);
  dict = Py_BuildValue("{s:i,s:i,s:i,s:f,s:i,s:i,s:i}",
		       "blocktype",blocktype,
		       "blockx",blockx,
		       "blocky",blocky,
		       "tilt",(float)linediff/ydiff,
		       "columns",darkzone_count/2,
		       "codes",codecount,
		       "ovals",ovalcount/2);
  if (!dict){
    Py_DECREF(list);
    return NULL;
  }
  PyList_Append(list,dict);
  for (counter=0;counter<darkzone_count;counter++){
    item = Py_BuildValue("[ii]", darkzone_start[counter],darkzone_end[counter]);
    if (!item){
      Py_DECREF(list);
      return NULL;
    }
    PyList_Append(list,item);
  }
  if (1){
    for (counter=0;counter<ovalcount;counter+=2){
      item = Py_BuildValue("[ii]", oval[counter],oval[counter+1]);
      if (!item){
	Py_DECREF(list);
	return NULL;
      }
      PyList_Append(list,item);
    }
  }
  for (counter=0;counter<codecount;counter++){
    item = Py_BuildValue("i", code[counter]);
    if (!item){
      Py_DECREF(list);
      return NULL;
    }
    PyList_Append(list,item);
  }

  return list ;
}

/* BALLOT ANALYSIS (works with RGB only) */
/* return a list with starting and ending y values of y dashes */
static inline PyObject*
getvdashes(Imaging im, int max4dark, int x1, int y1, int x2)
{
  int lastwasdark;
  int todark,tolight;
  PyObject *item;
  PyObject *list;
  int x, y, red;
  UINT8 *p;
  lastwasdark = 0;
  todark = 0;
  tolight = 0;

  list = PyList_New(0);
  for (y = y1; y < im->ysize; y++) {
    red = 0;
    for (x = x1; x < x2; x++) {
      p = (UINT8*) &im->image32[y][x];
      red += p[0];
    }  /* transition to white */
    red /= (x2-x1);
    if (lastwasdark && (red>=max4dark)){
      tolight = y;
      /* write y to the list */
      lastwasdark = 0;
      item = Py_BuildValue("ii", todark, tolight);
      if (!item){
	Py_DECREF(list);
	return NULL;
      }
      PyList_Append(list,item);
    }
    /* transition to dark */
    else if ((red<max4dark) && !lastwasdark){
      todark = y;
      /* write the dark start and the light start to the list */
      lastwasdark = 1;
    }
  }
  return list;
}

/* BALLOT ANALYSIS (works with RGB only) */
/* return a list with starting and ending y values of y dashes */
static inline PyObject*
gethdashes(Imaging im, int max4dark, int x1, int y1, int x2, int y2)
{
  int lastwasdark;
  int todark,tolight;
  PyObject *item;
  PyObject *list;
  int x, y, red;
  UINT8 *p;
  lastwasdark = 0;
  todark = 0;
  tolight = 0;

  list = PyList_New(0);
  for (x = x1; x < im->xsize; x++) {
    red = 0;
    for (y = y1; y < y2; y++) {
      p = (UINT8*) &im->image32[y][x];
      red += p[0];
    }  /* transition to white */
    red /= (y2-y1);
    if (lastwasdark && (red>=max4dark)){
      tolight = x;
      /* write y to the list */
      lastwasdark = 0;
      item = Py_BuildValue("ii", todark, tolight);
      if (!item){
	Py_DECREF(list);
	return NULL;
      }
      PyList_Append(list,item);
    }
    /* transition to dark */
    else if ((red<max4dark) && !lastwasdark){
      todark = x;
      /* write the dark start and the light start to the list */
      lastwasdark = 1;
    }
  }
  return list;
}

/* BALLOT ANALYSIS (works with RGB only) */
/* look for set of alternating light and dark stretches in vertical stripes */
/* return -1 if not found, or the x offset when the pattern is first seen */
static inline PyObject*
hasvdashes(Imaging im, int max4dark)
{
  UINT8 *p;
  int x,y;
  int red;
  int darks, lights, lastdarks, lastlights;
  int found;
  int tenth;
  int lastwasdark;
  lastwasdark = 0;
  found = -1;
  for (x = 0; x < im->xsize; x++) {
    darks = 0;
    lights = 0;
    lastdarks = 0;
    lastlights = 0;
    tenth = 0;
    for (y = 0; y < im->ysize; y++) {
      p = (UINT8*) &im->image32[y][x];
      red = p[0];
      if (lastwasdark) {
	if (red < max4dark) {
	  darks ++;
	  if (lastlights > 10 && lastdarks > 10 
	      && abs(lastlights-lights) <= tenth 
	      && abs(lastdarks - darks) <= tenth){
	    found = x;
	    break;
	  }
	}
	else {
	  lastdarks = darks;
	  lights ++;
	  tenth = lights/10;
	  lastwasdark = 0;
	}
      } else {
	if (red < max4dark) {
	  lastlights = lights;
	  darks ++;
	  lastwasdark = 1;
	} else {
	  lights ++;
	  tenth = lights/10;
	  if (lastlights > 10 && lastdarks > 10 
	      && abs(lastlights-lights) <= tenth 
	      && abs(lastdarks - darks) <= tenth){
	    found = x;
	    break;
	  }
	}
      }
    }
    if (found > -1) {
      break;
    }
  }
  return Py_BuildValue("i",found);
}


/* BALLOT ANALYSIS (works with RGB only) */
/* look for set of alternating light and dark stretches in vertical stripes */
/* return -1 if not found, or the y offset when the pattern is first seen */
static inline PyObject*
hashdashes(Imaging im, int max4dark)
{
  UINT8 *p;
  int x,y;
  int red;
  int darks, lights, lastdarks, lastlights,l2lights,l2darks;
  int found;
  int lastwasdark;
  lastwasdark = 0;
  found = -1;

  for (y = 0; y < im->ysize; y++) {
    darks = 0;
    lights = 0;
    lastdarks = 0;
    lastlights = 0;
    lastwasdark = 0;
    l2lights=0;
    l2darks=0;
    for (x = 0; x < im->xsize; x++) {
      p = (UINT8*) &im->image32[y][x];
      red = p[0];
      if (lastwasdark) {
	if (red < max4dark) {
	  darks ++;
	  if (lastlights > 10 && lastdarks > 10 
	      && abs(lastlights-lights) <= (lights/10) 
	      && abs(lastdarks - darks) <= (lights/10)
	      && abs(lastlights-l2lights) <= (lights/10) 
	      && abs(lastdarks - l2darks) <= (lights/10)){
	    found = y;
	    break;
	  }
	}
	else {
	  l2darks = lastdarks;
	  lastdarks = darks;
	  lights ++;
	  lastwasdark = 0;
	}
      } else {
	if (red < max4dark) {
	  l2lights = lastlights;
	  lastlights = lights;
	  darks ++;
	  lastwasdark = 1;
	} else {
	  lights ++;
	  if (lastlights > 10 && lastdarks > 10 
	      && abs(lastlights-lights) <= (lights/10) 
	      && abs(lastdarks - darks) <= (lights/10)
	      && abs(lastlights-l2lights) <= (lights/10) 
	      && abs(lastdarks - l2darks) <= (lights/10)){
	    found = y;
	    break;
	  }
	}
      }
    }
    if (found > -1) {
      break;
    }
  }
  return Py_BuildValue("i",found);
}

static inline PyObject*
diebolddashcode(Imaging im, int max4dark, int dpi, int starty)
{
  UINT8 *p;
  int x,y;
  int xcontig = 0;
  int ycontig = 0;
  int startx = 0;
  int foundx = 0;
  int foundy = 0;
  int startlastx = 0;
  int foundlastx = 0;
  int foundlasty = 0;
  int eighth = dpi/8;
  float distance = 0.;
  INT32 accum = 0;
  int n;
  // look for (x,y) of first dash at extreme left of image 
  // starting at starty and continuing upwards for one inch;
  // a dash will consist of at least 1/8" of dark pixels repeated for three rows
  foundx = 0;
  xcontig = 0;
  for( y = starty; y > (starty - dpi); y--){
    // if we failed to reach the necessary thickness of potential dash,
    // reset the starting point to zero for subsequent lines
    if (xcontig < eighth){
      printf("Setting startx back to zero at %d\n",y);
      startx = 0;
    }
    xcontig = 0;
    for (x = startx; x < startx + dpi; x++){
      p = (UINT8*) &im->image32[y][x];
      if (*p <= max4dark){
	xcontig++;
	if (xcontig > eighth){
	  foundx = x - xcontig;
	  foundx++;
	  foundy = y;
	  ycontig++;
	  printf("%d on line %d makes %d\n",xcontig,y,ycontig);
	  break;
	}
      }
      else {
	xcontig = 0;
      }
    }
    if (foundx>0){
      startx = foundx;
    }
    if (ycontig == dpi/32){ 
      break;
    }
    // found a dash ending at foundx+xcontig, foundy - ycontig
  }

  // look for last dash at extreme right of image following starty
  foundlasty = starty;
  foundlastx = im->xsize - 1 ;
  startlastx = im->xsize - 1 ;
  ycontig = 0;
  xcontig = 0;
  for( y = starty; y > (starty-dpi); y--){
    // if we failed to reach the thickness of a dash,
    // restart from the extreme right of the ballot for subsequent lines
    if (xcontig < eighth){
      startlastx = im->xsize - 1;
    }
    xcontig = 0;
    for (x = startlastx; x > (im->xsize - dpi); x--){
      p = (UINT8*) &im->image32[y][x];
      if (*p <= max4dark){
	xcontig++;
	if (xcontig > eighth){
	  foundlastx = x + xcontig;
	  foundlastx--;
	  foundlasty = y;
	  ycontig++;
	  break;
	}
      }
      else {
	xcontig = 0;
      }
    }
    if (foundlastx < startlastx){
      startlastx = foundlastx -1;
    }
    if (ycontig == (dpi/32)){ 
      break;
    }
  }
  // divide the space from the beginning of the first dash
  // to (the end of the last dash + 1/15") by 34, to generate the
  // interdash distance, then measure halfway into each dash
  // by adding the interdash distance to the first dash's start + 1/10"

  printf("x at left %d, at right %d\n",foundx,foundlastx);
  printf("y at left %d, at right %d\n",foundy, foundlasty);
  distance = (float)((foundlastx - foundx) + (dpi/15))/34.;
  // 1..33: skip the first and last, which will always be dark
  // leaves 32 darks or lights at each 1/4" over 8 inches, 
  // which allows us to generate and return a 32 bit code
  // representing the pattern of dark and light.
  for (n=1;n<33;n++){
    int checkx,checky,avg_intensity;
    UINT8 *pabove, *pbelow;
    checkx = (int)((foundx+(dpi/10)) + (n*distance));
    checky = (int)((((33-n)*foundy)+(n*foundlasty))/33.);
    printf(" x = %d\t",checkx);
    p = (UINT8*) &im->image32[checky][checkx];
    pabove = (UINT8*) &im->image32[checky-1][checkx];
    pbelow = (UINT8*) &im->image32[checky+1][checkx];
    avg_intensity = (int)((*p + *pabove + *pbelow)/3.);
    printf(" avg int: %d\t",avg_intensity);

    if (!(n%2)){
      printf("\n");
    }
    accum = (accum << 1);
    if (avg_intensity < 48){
      accum += 1;
    }
  }

  // of the last dash as a series of quarter inch zones.
  // set up accumulator with initial zero
  // for each quarter inch zone, add 1 to accumulator if zone is dark
  // left shift zone
  // THIS ASSUMES THAT AN INT32 is what Python expects for an int
  return(Py_BuildValue("i",accum));
}

/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject*
getdarkextents(Imaging im, int x1, int y1, int x2, int y2)
{
  UINT8 *p;
  int x,y,darkcount;
  int miny = 0;
  int maxy = 0;
  for (y=y1;y<y2;y++){
    darkcount = 0;
    for (x=x1;x<x2;x++){
      p = (UINT8*) &im->image32[y][x];
      if (*p < 64){
	darkcount++;
      }
      if (darkcount > 1) break;
    }
    if (darkcount > 1){
      if (miny==0){
	miny = y;
      }
      maxy = y;
    }
  }
  return Py_BuildValue("[ii]",miny,maxy);
}


/* BALLOT ANALYSIS (works with RGB only) */
/* look for set of contig pixels w/ intensity < max4dark spanning 1% width */
/* return -1 if not found, else the y offset into the provided image */
static inline PyObject*
getfirstdark(Imaging im, int max4dark)
{
  UINT8 *p;
  int x,y;
  int red;
  int horiz_contig;
  int hundredth;
  int found;
  int misses;
#ifdef VERBOSE
  printf("Entering get first dark.\n");
#endif
  for (y = 10; y < im->ysize; y++) {
    found = -1;
    horiz_contig = 0;
    hundredth = im->xsize/100;
    misses = 0;
    for (x = 0; x < im->xsize; x++) {
      p = (UINT8*) &im->image32[y][x];
      red = p[0];
      if (red < max4dark) {
	horiz_contig += misses;
	misses = 0;
	horiz_contig++;
	if (horiz_contig > hundredth){
	  found = y;
	  break;
	}
      }
      else {
	misses++;
	if (misses > 1){
	  horiz_contig = 0;
	  misses = 0;
	}
      }
    }
    if (found > -1){
      break;
    }
  }
  return Py_BuildValue("i",found);
}


/* getcolumnvlines works well for Hart ballot image.  The information
   it collects can then be used to search for horizontal lines "sprouting"
   from the vlines by searching the 1/16" on either side of the lines
   for dark pixels and, where found, extending the search and reporting
   those horizontal lines that extend at least one inch out.

   Because this search will start from vlines, the hlines found are
   automatically known to join the vlines, and can be treated as box
   corners.  Sprouting off to the right means a left box corner, sprouting
   off to the left means a right box corner.

   Assembly of left and right box corners gives a top or bottom with
   the sides.  The next available hline crossing the same pair of vlines
   is the other side of the box.

   The vops are thick lines that are 1/3" across, and the height of the 
   box including its lines is 1/6" and the lines are approx 1/32", so we
   can easily build lists of all vops in each box.

*/


typedef struct {
  int x1;
  int y1;
  int x2;
  int y2;
}Rect;


/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject *
gethartvoteboxes(Imaging im, int startx, int starty,  int dpi)
{
  /* Hart vote boxes will start approximately 1/8" from the column boundary
     and will include two thick horizontal lines extending approximately 1/3".
     These lines will be connected by vertical lines. */
  int quarter = dpi/4;
  int x, y, y2;
  int intensity;
  int last_intensity;
  int left2dark, right2dark, left2light, right2light;
  int contig, ycontig, x_at_contig;
  UINT8  *p,  *pnext, *pbelow;
  PyObject *list, *item;

  list = PyList_New(0);
  for (y = (starty+1); y < (im->ysize-(dpi/2));y++){ 
    contig = 0;
    ycontig = 0;
    left2dark = 0;
    right2dark = 0;
    left2light = 0;
    right2light = 0;
    last_intensity = intensity;
    p = (UINT8*) &im->image32[y][startx+quarter];
    intensity = p[0];
    if (intensity > 128){
      continue;
    }
    /* this may be a box, check for all conditions */
    /* first, box is 1/6" tall; 
       is there another dark pixel approx 1/7" down? */
    p = (UINT8*) &im->image32[y+(dpi/7)][startx+quarter];  
    intensity = p[0];
    if (intensity > 128){
      continue;
    }
    /* it's worth checking to see if the lines are more than 1/4" wide */
    for (x = startx; x < startx + (dpi/2); x++){
      /* check both the line beneath this line 
	 and the line 1/7" below this line */
      p = (UINT8*) &im->image32[y+1][x];  
      pbelow = (UINT8*) &im->image32[y+(dpi/7)][x];
      if ((p[0]<128) && (pbelow[0]<128)){
	contig++;
	x_at_contig = x;
      }
      else {
	contig = 0;
      }
      if (contig >= quarter){
	break;
	/* still in running */
      }
    }
    if (contig < quarter){
      continue;
    }
    /* reached here?  Means you found two 1/4" dark lines 1/7" apart */
    /* back up to the start of the top line and see if you find */
    /* a vertical connecting line running between the two */
    for (y2= y+1;y2 < (y+(dpi/7)); y2++){
      p = (UINT8*) &im->image32[y2][x_at_contig - contig + 1];
      pnext = (UINT8*) &im->image32[y2][x_at_contig - contig + 2];
      if ((p[0] < 128) || (pnext[0] < 128)){
	ycontig++;
      }
      else {
	ycontig = 0;
      }
      /* did you find 1/10" of dark pixels here or in the next column? */
      if (ycontig > (dpi/10)){
	/* add this to list of box ulc, */
	/* advance y by 1/6", */
	/* break out of inner for loop */
	item = Py_BuildValue("ii",x_at_contig-contig,y);
	if (!item){
	  Py_DECREF(list);
	  return NULL;
	}
	PyList_Append(list,item);
	y += (dpi/6);
	break;
      }
    }
  }
  return list;
}


/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject *
getpotentialhlines(Imaging im, int startx, int starty,  int dpi)
{

  int half = dpi/2;
  int twentieth = dpi/20;
  int x,y;
  int left_intensity, right_intensity;
  int last_left_intensity, last_right_intensity;
  int left2dark, right2dark, left2light, right2light;
  int disqualified;
  UINT8 *leftp, *rightp, *p, *pabove, *pbelow;
  PyObject *list, *item;
  int hundredth_inch = dpi/100;

  if (hundredth_inch < 1) {
    hundredth_inch = 1;
  }
  if (starty<hundredth_inch){
    starty = hundredth_inch;
  }
  // because we are checking for single pixel rows,
  // don't demand more than 75 pixels in row, no matter what dpi
  //if (half > 75) half=75;
  list = PyList_New(0);
  for (y = (starty+1); y < (im->ysize-(dpi/20));y++){ 
    left2dark = 0;
    right2dark = 0;
    left2light = 0;
    right2light = 0;
    last_left_intensity = left_intensity;
    last_right_intensity = right_intensity;
    leftp = (UINT8*) &im->image32[y][startx-twentieth];
    rightp = (UINT8*) &im->image32[y][startx+twentieth];
    left_intensity = leftp[0];
    right_intensity = rightp[0];

    // we need to adjust startx several times to accomodate tilt
    // so we look to confirm dark spot at startx; if not found,
    // we move left or right by one pixel to find dark spot
    if ((y>dpi) && ((y % (im->ysize/20)) == 0)){
      //
      UINT8 *p, *pbefore, *pafter, *pabove, *pabovebefore, *paboveafter;
      p = (UINT8*) &im->image32[y][startx];
      pbefore = (UINT8*) &im->image32[y][startx-1];
      pafter = (UINT8*) &im->image32[y][startx+1];
 
      pabove = (UINT8*) &im->image32[y- (dpi/4)][startx];
      pabovebefore = (UINT8*) &im->image32[y- (dpi/4)][startx-1];
      paboveafter = (UINT8*) &im->image32[y- (dpi/4)][startx+1];
	
      if (p[0]>128 && pabove[0]>128){
	if (pbefore[0]<=128 && pabovebefore[0]<=128){
	  startx--;
	}
	else if (pafter[0]<=128 && paboveafter[0]<=128){
	  startx++;
	}
      }
    }

    if ((left_intensity<128) && (last_left_intensity >= 128)){
      int red = 0;
      int lastred = 0;
      for (x=(startx-(twentieth+half));x<=(startx-twentieth);x++){
	p = (UINT8*) &im->image32[y][x];
	pabove = (UINT8*) &im->image32[y-hundredth_inch][x];
	red += p[0];
	lastred += pabove[0];
      }
      red /= half;
      lastred /= half;
      if ((red < 128) && (lastred >= 128)){
	left2dark = 1;
      }
    }
    else if ((last_left_intensity < 128) && (left_intensity >= 128)){
      int red = 0;
      int lastred = 0;
      for (x=(startx-(twentieth+half));x<=(startx-twentieth);x++){
	p = (UINT8*) &im->image32[y][x];
	pabove = (UINT8*) &im->image32[y-hundredth_inch][x];
	red += p[0];
	lastred += pabove[0];
      }
      red /= half;
      lastred /= half;
      if ((red >= 128) && (lastred < 128)){
	left2light = 1;
      }
    }
    if ((right_intensity<128) && (last_right_intensity >= 128)){
      int red = 0;
      int lastred = 0;
      for (x=(startx+twentieth);x<=(startx+twentieth+half);x++){
	p = (UINT8*) &im->image32[y][x];
	pabove = (UINT8*) &im->image32[y-hundredth_inch][x];
	red += p[0];
	lastred += pabove[0];
      }
      red /= half;
      lastred /= half;
      if ((red < 128) && (lastred >= 128)){
	right2dark = 1;
      }
    }

    else if ((last_right_intensity < 128) && (right_intensity >= 128)){
      int red = 0;
      int lastred = 0;
      for (x=(startx+twentieth);x<=(startx+twentieth+half);x++){
	p = (UINT8*) &im->image32[y][x];
	pabove = (UINT8*) &im->image32[y-hundredth_inch][x];
	red += p[0];
	lastred += pabove[0];
      }
      red /= half;
      lastred /= half;
      if ((red >= 128) && (lastred < 128)){
	right2light = 1;
      }
    }
    if (left2dark || left2light){
      /* append to left list if, for each x position */
      /* between startx-half and startx, */
      /* either this line's pixel or the one 1/100" above or the one below */
      /* is the same side of 128 as this pixel */
      disqualified = 0;
      for (x=(startx-(twentieth+half));x<=(startx-twentieth);x++){
	p = (UINT8*) &im->image32[y][x];
	pabove = (UINT8*) &im->image32[y-hundredth_inch][x];
	pbelow = (UINT8*) &im->image32[y+hundredth_inch][x];
	/* went dark, but no relevant pixel is dark here: disqualify */
	if (left2dark && 
	    (!(p[0] < 128 || pabove[0] < 128 || pbelow[0] < 128))){
	  disqualified++;
	}
	/* went light, but no relevant pixel is light here: disqualify */
	if (left2light && 
	    (!(p[0] >= 128 || pabove[0] >= 128 || pbelow[0] >= 128))){
	  disqualified++;
	}
	if (disqualified > (dpi/35)){
	  break;
	}
      }
      if (disqualified <= (dpi/35)){
	/* not disqualified, add to list of potential hlines */
	item = Py_BuildValue("i",-y);
	if (!item){
	  Py_DECREF(list);
	  return NULL;
	}
	PyList_Append(list,item);
      }
      else {
	left2dark = 0;
	left2light = 0;
      }
    }
    if (right2dark || right2light){
      /* append to right list if, for each x position */
      /* between startx and startx+half, */
      /* either this line's pixel or the one above or the one below */
      /* is the same side of 128 as this pixel */
      disqualified = 0;
      for (x=(startx+twentieth);x<=(startx+twentieth+half);x++){
	p = (UINT8*) &im->image32[y][x];
	pabove = (UINT8*) &im->image32[y-hundredth_inch][x];
	pbelow = (UINT8*) &im->image32[y+hundredth_inch][x];
	/* went dark, but no relevant pixel is dark here: disqualify */
	if (right2dark && 
	    (!(p[0] < 128 || pabove[0] < 128 || pbelow[0] < 128))){
	  disqualified++;
	}
	/* went light, but no relevant pixel is light here: disqualify */
	if (right2light && 
	    (!(p[0] >= 128 || pabove[0] >= 128 || pbelow[0] >= 128))){
	  disqualified++;
	}
	if (disqualified > (dpi/35)){
	  break;
	}
      }
      if (disqualified <= (dpi/35)){
	/* not disqualified, add to list of potential hlines */
	item = Py_BuildValue("i",y);
	if (!item){
	  Py_DECREF(list);
	  return NULL;
	}
	PyList_Append(list,item);
      }
      else {
	right2dark = 0;
	right2light = 0;
      }
    }
  }
  /* return list of potential hlines */
  return list;
}


/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject *
getcolumnvlines(Imaging im, int startx, int starty, int endx)
{
  UINT8 *p;
  UINT8 *pbefore, *pafter;
  int x, y2;
  int dark_x[50];
  int dark_x_count = 0;
  int counter = 0;
  PyObject *list, *item;
  /* look for dark/light transitions that extend vertically for at least 100 */
  for (x=startx;x<endx;x++){
    p = (UINT8*) &im->image32[starty][x];
    pbefore = (UINT8*) &im->image32[starty][x-2];
    pafter = (UINT8*) &im->image32[starty][x+2];

    //if (p[0]<128)printf("(%d,%d) p[0]=%d before %d after %d\n",x,starty,p[0],pbefore[0],pafter[0]);
    if ((p[0] < 128) 
	&& ((pbefore[0] >= 128) || (pafter[0] >= 128))
	){
      /* three darks at a transition, worth checking for more */
      counter = 0;
      for (y2=starty+2;y2<starty+100;y2++){
	/* allow 1% off vertical by checking before and after */
	p = (UINT8*) &im->image32[y2][x];
	pbefore = (UINT8*) &im->image32[y2][x-1];
	pafter = (UINT8*) &im->image32[y2][x+1];
	if ((p[0]<128) || (pbefore[0]<128) || (pafter[0]<128)){
	  counter++;
	}
      }
#ifdef VERBOSE
      printf("Counter=%d at x=%d\n",counter,x);
#endif
      if (counter > 90){
	dark_x[dark_x_count] = x;
	dark_x_count++;
	if (dark_x_count >= 50)break;
      }
    } /* end three darks */
  } /* end for x */
  /* build a list of all dark x's, */
  list = PyList_New(0);
  for (x=0;x<dark_x_count;x++){
    /* append this x value to returned list */
    item = Py_BuildValue("i",dark_x[x]);
    if (!item){
      Py_DECREF(list);
      return NULL;
    }
    PyList_Append(list,item);
  }
  return list;
}

/* BALLOT ANALYSIS (works with RGB only) */
static inline PyObject*
getlines(Imaging im, int max4dark, int allowed_misses)
{

  Rect working[50];
  int max_working = 49;
  Rect lel;
  int working_count = 0;
  int c;
  int replaced = 0;
  int appended = 0;
  int adjusted = 0;
  UINT8 *p;
  int x,y;
  int red;
  int horiz_contig;
  int vert_contig;
  PyObject *list;
  int max_contig, max_contig_x, max_contig_y;
  int minlength;
  int misses;

  minlength = im->xsize/10;
  list = PyList_New(0);
 
  /* first, find horizontal lines, add x1,y1,x2,y2 to list */
  for (y = 0; y < im->ysize; y++) {
    horiz_contig = 0;
    max_contig = 0;
    max_contig_x = 0;
    misses = 0;
    adjusted = 0;
    for (x = 0; x < im->xsize; x++) {
      p = (UINT8*) &im->image32[y][x];
      red = p[0];
      if (red < max4dark) {
	horiz_contig += misses;
	misses = 0;
	horiz_contig++;
	if (horiz_contig > max_contig){
	  max_contig = horiz_contig;
	  max_contig_x = x;
	}
      }
      else {
	if (horiz_contig>0){
	  misses++;
	}
	if ((misses > allowed_misses) && (horiz_contig<=minlength)){
	  misses = 0;
	  horiz_contig = 0;
	}
	if ((misses > allowed_misses) && (horiz_contig>minlength)){
	  /* check to see if we've exceeded minimum required length */
	  /* and write out a line segment if we have */
	  replaced = 0;
	  appended = 0;
	  lel.x1 = max_contig_x - horiz_contig;
	  lel.y1 = y;
	  lel.x2 = max_contig_x;
	  lel.y2 = y;
	  for (c=0;c<working_count;c++){
	    if ( (working[c].y2 == (lel.y1-1)) 
		 && ((lel.x1 >= working[c].x1 && lel.x1 <=working[c].x2)
		     || (lel.x2 >=working[c].x1 && lel.x2 <= working[c].x2)
		     || (lel.x1 <= working[c].x1 && lel.x2 >= working[c].x2)) ){
	      working[c].x1 = min(lel.x1,working[c].x1);
	      working[c].x2 = max(lel.x2,working[c].x2);
	      working[c].y2 = lel.y2;
	      replaced++;
	      adjusted++;
	    }
	  }
	  if (replaced==0){
	    working[working_count].x1 = lel.x1;
	    working[working_count].y1 = lel.y1;
	    working[working_count].x2 = lel.x2;
	    working[working_count].y2 = lel.y2;
	    working_count++;
	    appended = 1;
	    adjusted++;
	  }
	  horiz_contig = 0;
	  max_contig = 0;
	  misses = 0;
	}
      }
    }
    if ((adjusted == 0) || (working_count >= max_working)){
      /* we made no changes on this line, */
      /* all working lines are complete */
      /* move contents of working to python list */
      /* and reset working_count to 0 */
      for (c=0;c<working_count;c++){
	PyObject *item;
	/* if the dark stretch is too thick to be a line, 
	   split it into a thinline at the top 
	   and a thinline at the bottom */
	if ((working[c].y2 - working[c].y1)>40){
	  /* build and append first value */
	  item = Py_BuildValue("iiii",
			       working[c].x1,
			       working[c].y1,
			       working[c].x2,
			       working[c].y1+5);
	  if (!item){
	    Py_DECREF(list);
	    return NULL;
	  }
	  PyList_Append(list,item);
	  /* build second value, appended after if/else */
	  item = Py_BuildValue("iiii",
			       working[c].x1,
			       working[c].y2-5,
			       working[c].x2,
			       working[c].y2);
	} else {
	  item = Py_BuildValue("iiii",
			       working[c].x1,
			       working[c].y1,
			       working[c].x2,
			       working[c].y2);
	}
	if (!item){
	  Py_DECREF(list);
	  return NULL;
	}
	PyList_Append(list,item);
      }
      working_count = 0;
    }
  }

  /* repeat for vertical lines, add x1,y1,x2,y2 to list */
  working_count = 0;

  minlength = im->ysize/10;
  for (x = 0; x < im->xsize; x++) {
    vert_contig = 0;
    max_contig = 0;
    max_contig_y = 0;
    misses = 0;
    adjusted = 0;
    for (y = 0; y < im->ysize; y++) {
      p = (UINT8*) &im->image32[y][x];
      red = p[0];
      if (red < max4dark) {
	vert_contig += misses;
	misses = 0;
	vert_contig++;
	if (vert_contig > max_contig){
	  max_contig = vert_contig;
	  max_contig_y = y;
	}
      }
      else {
	if (vert_contig>0){
	  misses++;
	}
	if ((misses > allowed_misses) && (vert_contig<=minlength)){
	  misses = 0;
	  vert_contig = 0;
	}
	if ((misses > allowed_misses) && (vert_contig>minlength)){
	  /* check to see if we've exceeded minimum required length */
	  /* and write out a line segment if we have */
	  replaced = 0;
	  appended = 0;
	  lel.x1 = x;
	  lel.y1 = max_contig_y - vert_contig;
	  lel.x2 = x;
	  lel.y2 = max_contig_y;
	  for (c=0;c<working_count;c++){
#ifdef VERBOSE
	    printf("Working count %d WORKING %d %d %d %d NEW %d %d %d %d\n",
		   working_count,
		   working[c].x1,
		   working[c].y1,
		   working[c].x2,
		   working[c].y2,
		   lel.x1,lel.y1,lel.x2,lel.y2);
#endif
	    if ( (working[c].x2 == (lel.x1-1)) 
		 &&((lel.y1 >= working[c].y1 && lel.y1 <=working[c].y2)
		 || (lel.y2 >=working[c].y1 && lel.y2 <= working[c].y2)
		    || (lel.y1 <= working[c].y1 && lel.y2 >= working[c].y2)) ){
	      working[c].x2 = lel.x2;
	      working[c].y1 = min(lel.y1,working[c].y1);
	      working[c].y2 = max(lel.y2,working[c].y2);
	      replaced++;
	      adjusted++;
	    }
	    if ( (working[c].x1 == lel.x1) 
		 && (working[c].x2 == lel.x2) 
		 &&(lel.y1 == working[c].y1 )
		 && (lel.y2 ==working[c].y2 )
		 ){
	      working[c].x2 = lel.x2;
	      working[c].y1 = min(lel.y1,working[c].y1);
	      working[c].y2 = max(lel.y2,working[c].y2);
#ifdef VERBOSE
	      printf("NOT ADDING identical line.\n");
#endif
	      replaced++;
	      adjusted++;
	    }
	  }
	  if (replaced==0){
	    working[working_count].x1 = lel.x1;
	    working[working_count].y1 = lel.y1;
	    working[working_count].x2 = lel.x2;
	    working[working_count].y2 = lel.y2;
	    working_count++;
	    appended = 1;
	    adjusted++;
	  }
	  vert_contig = 0;
	  max_contig = 0;
	  misses = 0;
	}
      }
    }
    if ((adjusted == 0) || (working_count >= max_working)){
      /* we made no changes on this line, */
      /* all working lines are complete */
      /* move contents of working to python list */
      /* and reset working_count to 0 */
      //if (working_count>0){
      //	printf("MOVING %d TO LIST.\n",working_count);
      //}
      for (c=0;c<working_count;c++){
	PyObject *item;
	if ((working[c].x2 - working[c].x1)>40){
	  item = Py_BuildValue("iiii",
			       working[c].x1,
			       working[c].y1,
			       working[c].x1+5,
			       working[c].y2);
	  if (!item){
	    Py_DECREF(list);
	    return NULL;
	  }
	  PyList_Append(list,item);
	  item = Py_BuildValue("iiii",
			       working[c].x2-5,
			       working[c].y1,
			       working[c].x2,
			       working[c].y2);
	} else {
	item = Py_BuildValue("iiii",
			     working[c].x1,
			     working[c].y1,
			     working[c].x2,
			     working[c].y2);
	}
	if (!item){
	  Py_DECREF(list);
	  return NULL;
	}
	PyList_Append(list,item);
      }
      working_count = 0;
    }
  }

  /* this will work only for RGB */
  if (im->image32 != NULL) {
    p = (UINT8*) &im->image32[y][x];
    switch (im->type) {
    case IMAGING_TYPE_UINT8:
      /* unsigned integer */
      if (im->bands == 2)
	break;
      if (im->bands == 3)
	return list;
    case IMAGING_TYPE_INT32:
      /* signed integer */
      return PyInt_FromLong(0x01020305);
    case IMAGING_TYPE_FLOAT32:
      /* floating point */
      return PyFloat_FromDouble(0x01020306);
    }
  }

  /* unknown type */
  Py_INCREF(Py_None);
  return Py_None;
}


/* BALLOT ANALYSIS (works with RGB only) */
/* support function */
static inline int within(int a, int b, int c)
{
  return (abs(b-a)<=c);
}


/* BALLOT ANALYSIS (works with RGB only) */
/* find y-offsets with completely white lines at least .95 of width */
/* and x-offsets with completely white lines at least .95 of height */
static inline PyObject*
getgaps(Imaging im, int max4dark, int allowed_misses, int horiz_only)
{
    UINT8 *p;
    int x,y;
    int lastx,lasty;
    int red;
    int horiz_contig;
    int vert_contig;
    PyObject *list;
    PyObject * item;
    int max_contig, max_contig_x, max_contig_y;
    int last_max_contig, last_max_contig_x, last_max_contig_y;
    int minlength;
    int misses;
    int matchlines;
    matchlines = 0;
    minlength = (39*im->xsize)/40;
    list = PyList_New(0);

    /* first, find horizontal gaps, add x1,y1,x2,y2 to list */
    last_max_contig_x = 0;
    last_max_contig = 1;
    lasty = 0;
    for (y = 0; y < im->ysize; y++) {
      horiz_contig = 0;
      max_contig = 0;
      max_contig_x = 0;
      misses = 0;
      for (x = 0; x < im->xsize; x++) {
	  p = (UINT8*) &im->image32[y][x];
	  red = p[0];
	  if (red >= max4dark) {
	    horiz_contig += misses;
	    misses = 0;
	    horiz_contig++;
	    if (horiz_contig > max_contig){
	      max_contig = horiz_contig;
	      max_contig_x = x;
	    }
	  }
	  else {
	    misses++;
	    if (misses > allowed_misses){
	      horiz_contig = 0;
	      misses = 0;
	    }
	  }
      }
      if (max_contig > minlength){
	/* see if this matches previous lines to within 1 pixel */
	if (y == (lasty + 1)){
	  /* don't add this to the list, instead increment matchlines */
	  matchlines++;
	}
	else {
	  if (lasty > 0){
	    item = Py_BuildValue("iiii",  
				 last_max_contig_x - last_max_contig + 1, 
				 lasty-matchlines, 
				 last_max_contig_x + 1, 
				 lasty);
	    PyList_Append(list,item);
	    matchlines = 0;
	  }
	}
	last_max_contig_x = max_contig_x;
	last_max_contig = max_contig;
	lasty = y;
      }
      /* put last gap at end of list, so last preceding text is caught 
      item = Py_BuildValue("iiii",last_max_contig_x - last_max_contig + 1,
			   lasty-matchlines,
			   last_max_contig_x + 1,
			   im->ysize);
			   PyList_Append(list,item);*/

	
    }

    if (!horiz_only){
      /* repeat for vertical lines, add x1,y1,x2,y2 to list */
      minlength = (2*im->ysize/3);
      last_max_contig_y = 0;
      last_max_contig = 1;
      lastx = 0;
      matchlines = 0;
      for (x = 0; x < im->xsize; x++) {
	vert_contig = 0;
	max_contig = 0;
	max_contig_y = 0;
	misses = 0;
	for (y = 0; y < im->ysize; y++) {
	  p = (UINT8*) &im->image32[y][x];
	  red = p[0];
	  if (red >= max4dark) {
	    vert_contig += misses;
	    misses = 0;
	    vert_contig++;
	    if (vert_contig > max_contig){
	      max_contig = vert_contig;
	      max_contig_y = y;
	    }
	  }
	  else {
	    misses++;
	    if (misses > allowed_misses){
	      vert_contig = 0;
	      misses = 0;
	    }
	  }
	}
	if (max_contig > minlength){
	  /* see if this matches previous line except for 1 pix advance */
	  if (within(max_contig_y,last_max_contig_y,1) &&
	      within(max_contig,last_max_contig,1) &&
	      x == (lastx + 1)){
	    /* don't add this to the list, instead increment matchlines */
	    matchlines++;
	  } else {
	    if (lastx > 0){
	      item = Py_BuildValue("iiii", 
				   lastx-matchlines, 
				   last_max_contig_y - last_max_contig + 1, 
				   lastx,  
				   last_max_contig_y + 1);
	      PyList_Append(list,item);
	      matchlines = 0;
	    }
	  }
	  last_max_contig_y = max_contig_y;
	  last_max_contig = max_contig;
	  lastx = x;
	}
      }
    }
    /* this will work only for RGB */
    if (im->image32 != NULL) {
        p = (UINT8*) &im->image32[y][x];
        switch (im->type) {
        case IMAGING_TYPE_UINT8:
            /* unsigned integer */
            if (im->bands == 2)
                break;
            if (im->bands == 3)
	      return list;
        case IMAGING_TYPE_INT32:
            /* signed integer */
            return PyInt_FromLong(0x01020305);
        case IMAGING_TYPE_FLOAT32:
            /* floating point */
            return PyFloat_FromDouble(0x01020306);
        }
    }

    /* unknown type */
    Py_INCREF(Py_None);
    return Py_None;
}



/* BALLOT ANALYSIS (works with RGB only) */
/* a branch ends when a link's start and end are both 0 */
typedef struct _Link {
  int line;
  int endline;
  int start;
  int end;
  struct _Link *branch1;
  struct _Link *branch2;
  struct _Link *next;
  struct _Link *prev;
}  *LinkPtr, Link;


/* BALLOT ANALYSIS (works with RGB only) */
typedef struct _MinMax{
  int min_x;
  int max_x;
} *MinMaxPtr, MinMax;

typedef struct _BBox{
  int min_x;
  int max_x;
  int min_y;
  int max_y;
} *BBoxPtr, BBox;

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject *
getbigglyphs(Imaging im, int minw, int minh )
{
  PyObject *retlist;
  int pty = 0;
  int ptx = 0;
  BBox candidates[250];
  int max_candidates = 250;
  int candidate_count = 0;
  int ccount, ccount2; /* for use in for loops */
  UINT8 *p;

  retlist = PyList_New(0);

  for (pty = 0; pty < im->ysize; pty++) {
    int runlength;
    runlength = 0;
    for (ptx = 0; ptx < im->xsize; ptx++) {
      p = (UINT8*) &im->image32[pty][ptx];
      /* dark pixels extend run */
      if (*p < 64){
	runlength++;
      }
      /* light pixels trigger run length check, set run length to zero */
      else { 
	if (runlength >= minw && (runlength < (5*minw))){
	  /* this row might be part of a big glyph, */
	  /* but not part of a huge glyph (a box) */
	  BBox new_candidate;
	  int ccount;
	  int extended_a_candidate = 0;
	  new_candidate.min_x = ptx - runlength;
	  new_candidate.max_x = ptx; 
	  new_candidate.min_y = pty;
	  for (ccount=0;ccount < candidate_count; ccount++){
	    /* if this begins at or before the end of a candidate */
	    /* and this ends at or after the beginning of that candidate */
	    /* and this is within a line of the max_y of that candidate */
	    /* then modify that candidate to include this */
	    if ((new_candidate.min_x <= candidates[ccount].max_x)
		&& (new_candidate.max_x >= candidates[ccount].min_x)
		&& ((new_candidate.min_y - candidates[ccount].max_y) <= 1)){
	      /* modify candidates[ccount] */
	      candidates[ccount].max_y = new_candidate.min_y;
	      candidates[ccount].min_x = min(candidates[ccount].min_x,new_candidate.min_x);
	      candidates[ccount].max_x = max(candidates[ccount].max_x,new_candidate.max_x);
	      extended_a_candidate++;
	    }
	  }
	  if (extended_a_candidate == 0){
	    /* add the new_candidate to the candidate list */
	    candidates[candidate_count].min_x = new_candidate.min_x;
	    candidates[candidate_count].max_x = new_candidate.max_x;
	    candidates[candidate_count].min_y = new_candidate.min_y;
	    candidates[candidate_count].max_y = new_candidate.min_y;
	    candidate_count++;
	    if (candidate_count >= max_candidates){
	      Py_DECREF(retlist);
	      return NULL;
	    }
	  }
	} /* we've processed the lighter pixel */
	runlength = 0; /* because we encountered a lighter pixel */
      } /* end of light pixel handling */


    } /* end of row */
    /* at end of row, process all candidates that did not extend
       into the row; if they are tall enough, copy to return list, 
       regardless, remove from candidate array and pack array down */
    for (ccount = 0;ccount < candidate_count; ccount++){
      if (candidates[ccount].max_y < pty){
	if ((candidates[ccount].max_y - candidates[ccount].min_y)>=minh){
	  /* copy candidates[ccount] into return list */
	  PyObject *item;

	  item = Py_BuildValue("iiii", 
			       candidates[ccount].min_x,
			       candidates[ccount].min_y,
			       candidates[ccount].max_x,
			       candidates[ccount].max_y);
	  if (!item){
	    Py_DECREF(retlist);
	    return NULL;
	  }
	  PyList_Append(retlist,item);
	}
	/* move all higher candidates down, overwriting this one */
	/* and reduce candidate_count by one */
	for (ccount2 = ccount ; ccount2 < (candidate_count-1) ; ccount2++){
	  candidates[ccount2].min_x = candidates[ccount2+1].min_x;
	  candidates[ccount2].max_x = candidates[ccount2+1].max_x;
	  candidates[ccount2].min_y = candidates[ccount2+1].min_y;
	  candidates[ccount2].max_y = candidates[ccount2+1].max_y;
	}
	candidate_count--;
	ccount--; /* having just put a new candidate in the exam spot */
      }
    } /* end of all rows */
  }
  return retlist;
}
/* BALLOT ANALYSIS (works with RGB only) */
static PyObject *
getblobs_fromfunc(Imaging im, int x, int y, int w, int h, int minw, int minh, int testfuncarg, int (*testfunc)(UINT8 *,int) )
{
  PyObject *     retlist;
  int link_allocation_count = 0;
  int ptx, pty;
  LinkPtr newlink;
  LinkPtr lastlink;
  LinkPtr rootlink; 
  LinkPtr testlink;
  LinkPtr nextlink;
  LinkPtr freelink;
  LinkPtr blob;
  LinkPtr prevblob;
  LinkPtr lastblob;
  int allocated_links = 1;
  int links_from_line = 0;
  int light;
  UINT8 *p;
  lastblob = NULL;
  prevblob = NULL;
  blob = NULL;

  retlist = PyList_New(0);
  newlink = (LinkPtr)NULL;
  lastlink = calloc(sizeof(Link),1);
  link_allocation_count++;
  /* rootlink will always be the first allocated link */
  rootlink = lastlink;


  for (pty = y; pty < (y+h); pty++) {
    light = 1;
    links_from_line = 0;
    for (ptx = x; ptx < (x+w); ptx++) {
      p = (UINT8*) &im->image32[pty][ptx];
      if (light){
	if ((*testfunc)(p,testfuncarg)){
	  /* entering dark zone, create link, set start */
	  newlink  = calloc(sizeof(Link),1);
	  link_allocation_count++;
	  newlink->line = pty;
	  newlink->endline = pty;
	  newlink->start = ptx;
	  newlink->prev = lastlink; 
	  lastlink->next = newlink;
	  light = 0;
	  links_from_line++;
	  allocated_links++;
	} 
      }
      else {
	if (! (*testfunc)(p,testfuncarg)){
	  /* exiting dark zone, complete link by setting end */
	  newlink->end = ptx;
	  lastlink = newlink;
	  light = 1;
	  /* search all links from prev row for overlap with this link,     */
	  /* assign first overlapping link (if any) as this link's branch1, */
	  /* assign second overlapping link (if any) as this link's branch2 */
	  for (testlink = newlink->prev; 
	       (testlink) && (testlink != rootlink) 
		 && (testlink->endline >= (newlink->endline -1)); 
	       testlink = testlink->prev) {
	    /* testlink is on previous line and both */
	    /* test starts before new ends and test ends after new starts */
	    if ((testlink->endline == (newlink->endline - 1)) 
		&& (((testlink->start - 1) <= newlink->end) 
		    && (testlink->end >= (newlink->start - 1)))){
	      if (newlink->branch1){
#ifdef VERBOSE
#endif
		newlink->branch2 = testlink;
	      } else {
#ifdef VERBOSE
#endif
		newlink->branch1 = testlink;
	      }
	    }
	  }
	}
      } /* end of else */

    } /* end of for x */

    if (newlink && !light){
      newlink->end = x+w;
      lastlink = newlink;
      light = 1;
      /* search all links from prev row for overlap with this link, */
      /* assign first overlapping link (if any) as this link's branch1, */
      /* assign second overlapping link (if any) as this link's branch2 */
      for (testlink = newlink->prev; 
	   (testlink) && (testlink != rootlink) 
	     && (testlink->endline >= (newlink->endline -1)); 
	   testlink = testlink->prev) {
	if ((testlink->endline == (newlink->endline - 1)) 
	    && (((testlink->start - 1) <= newlink->end) 
		&& (testlink->end >= (newlink->start - 1)))){
	  if (newlink->branch1){
#ifdef VERBOSE
	    printf("Linking new %x to %x via branch2\n",newlink,testlink);
#endif
	    newlink->branch2 = testlink;
	  } else {
#ifdef VERBOSE
	    printf("Linking new %x to %x via branch1\n",newlink,testlink);
#endif
	    newlink->branch1 = testlink;
	  }
	}
      }
    }
    /* still at end of row */
    /* merge link with those of previous line at the end of each line */
    if (lastlink && lastlink->prev){
      for (testlink = lastlink;testlink;testlink = nextlink){
	if (lastlink->endline == 18 || lastlink->endline == 17){
#ifdef VERBOSE
	  printf("Row %d testlink %x b1 %x b2 %x st %d en %d li %d endli %d\n",
		 lastlink->endline,
		 testlink,
		 testlink->branch1,
		 testlink->branch2,
		 testlink->start,
		 testlink->end,
		 testlink->line,
		 testlink->endline);

#endif
	}
	nextlink = testlink->prev;
	if (testlink->endline < lastlink->endline)continue;
	if (testlink->branch2 
	    /*&& (testlink->branch2->endline != 0)*/
	      && (testlink->branch2->endline >= (lastlink->endline -1 ))){
	  testlink->line = min(testlink->branch2->line,testlink->line);
	  testlink->endline = max(testlink->branch2->endline,testlink->endline);
	  testlink->start = min(testlink->branch2->start,testlink->start);
	  testlink->end = max(testlink->branch2->end,testlink->end);
	  testlink->branch2->start = 0;
	  testlink->branch2->end = 0;
	  testlink->branch2->line = 0;
	  testlink->branch2->endline = 0;
	}
      }
      for (testlink = lastlink;testlink;testlink = nextlink){
#ifdef VERBOSE
	printf("TL %x %d %d %d %d\n",
	       testlink,
	       testlink->start,testlink->line,
	       testlink->end,testlink->endline);
	
#endif
	nextlink = testlink->prev;
	if (testlink->endline < lastlink->endline)continue;
	/* must use >= here, because testlink's endline may already have been
	   increased as a result of branch 2 merge */
	if (testlink->branch1
	    /*&& (testlink->branch1->endline != 0)*/
	      && (testlink->branch1->endline >= (lastlink->endline -1 ))){
#ifdef VERBOSE
	  printf("Testlink %x %d %d %d %d testlink branch1 %x %d %d %d %d \n",
		 testlink,
		 testlink->start,testlink->line,
		 testlink->end,testlink->endline,
		 testlink->branch1,
		 testlink->branch1->start,testlink->branch1->line,
		 testlink->branch1->end,testlink->branch1->endline);
#endif	  
	  testlink->line = min(testlink->branch1->line,testlink->line);
	  testlink->endline = max(testlink->branch1->endline,testlink->endline);
	  testlink->start = min(testlink->branch1->start,testlink->start);
	  testlink->end = max(testlink->branch1->end,testlink->end);
	  testlink->branch1->start = 0;
	  testlink->branch1->end = 0;
	  testlink->branch1->line = 0;
	  testlink->branch1->endline = 0;
#ifdef VERBOSE
	  printf("Adj testlink %x %d %d %d %d\n",
		 testlink,
		 testlink->start,testlink->line,
		 testlink->end,testlink->endline);
#endif	  
	}
      }	    
      /*
      for (testlink = lastlink;testlink;testlink = nextlink){
	nextlink = testlink->prev;
	if (testlink->branch2){
	  testlink->branch2->start = 0;
	  testlink->branch2->end = 0;
	  testlink->branch2->line = 0;
	  testlink->branch2->endline = 0;
	}
	if (testlink->branch1){
	  testlink->branch1->start = 0;
	  testlink->branch1->end = 0;
	  testlink->branch1->line = 0;
	  testlink->branch1->endline = 0;
	}
      }
      */

    } /* still at end of row */


    /* When you encounter a line without black pixels, you can
       turn your links into blobs, and throw away the link network
       that has not become part of the blob network. */

    if ((links_from_line == 0) && (allocated_links > 1)){
      /* process link set to here and free them as follows;
	 starting with last item created, save its prev for next round
	 if non-NULL branch, merge its start and end and line with those 
	 of its branch, move to next and delete the one just processed.
	 if NULL branch, make the link a blob
	 Continue */
 
      for (testlink = lastlink;testlink;testlink = nextlink){
	nextlink = testlink->prev;
	if (testlink->endline>0){
	  testlink->prev = lastblob;
	  lastblob = testlink;
	}
      }
      for (blob = lastblob;blob;blob=prevblob){
	PyObject * item;
	if ((blob->end > 0) 
	    && ((blob->end - blob->start)>=minw)
	    && ((blob->endline - blob->line)>=minh)
	    ){
	  item = Py_BuildValue("iiii", 
			       blob->start,
			       blob->line,
			       blob->end,
			       blob->endline);
	  if (!item){
	    Py_DECREF(retlist);
	    return NULL;
	  }
	  PyList_Append(retlist,item);
	}
	prevblob = blob->prev;
      }
      /* now free all links from lastlink back to rootlink */
      {LinkPtr link;
	for (freelink = rootlink;1;freelink = link){
	  link = freelink->next;
	  free(freelink);
	  link_allocation_count--;
	  if (!link){ 
	    break;
	  }
	  if (link_allocation_count == 0) {
	    break;
	  }
	}
      }
      /* reset variables for next blob batch */
      allocated_links = 1;
      newlink = (LinkPtr)NULL;
      lastlink = calloc(sizeof(Link),1);
      rootlink = lastlink;
      link_allocation_count++;
      lastblob = NULL;
      prevblob = NULL;
      blob = NULL;

    }
    /* we are now ready to start the next line */
    /* if the previous line had no black pixels, */
    /* we should be starting from the root link, */
    /* otherwise, from the last link created */
  }
  /* finally, free the root link */
  //free(rootlink);
  //link_allocation_count--;
  return retlist;
}
	


/* BALLOT ANALYSIS (works with RGB only) */
static int is_darker_than(UINT8 *p, int val)
{
  return (p[0] < val);
}


/* BALLOT ANALYSIS (works with RGB only) */
static int is_tinted_by(UINT8 *p, int val)
{
  /* WARNING: val is ignored */
  return (abs(p[0]-p[1]) > 20) || (abs(p[0]-p[2]) > 20) || (abs(p[1]-p[2]) > 20);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject *
getblobs(Imaging im, int x, int y, int w, int h, int testfuncarg)
{
  return getblobs_fromfunc(im,x,y,w,h,0,0, testfuncarg,&is_darker_than);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject *
getwideblobs(Imaging im, int x, int y, int w, int h, int minw, int minh, int testfuncarg)
{
  return getblobs_fromfunc(im,x,y,w,h,minw,minh, testfuncarg, &is_darker_than);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject *
getdieboldvoteovals(Imaging im, int x, int y, int w, int h, int ow, int oh )
{
  PyObject *     retlist;
  PyObject *     item;
  int n;
  int pty, ptx, ptx2;
  int scan_from_x;
  int oval_startx = 0;
  int contig_tinted = 0;
  int oval_line = 0;
  int oval_start = 0;
  int oval_confirmed = 0;
  UINT8 *p_r, *p_g, *p_b;
  UINT8 *p_r2, *p_g2, *p_b2;

  retlist = PyList_New(0);
  // look in designated bounding box for a pair of lines 
  // at least ow long and separated by oh, 
  // with at least two tinted pixels on each scanline enclosed by the pair

  // this for loop will need to be repeated with the bounding box
  // adjusted to exclude any ovals found in first pass, so that we can
  // search for additional ovals past the first in this y zone of the ballot
  scan_from_x = x;
  for(n=0;n<2;n++){
  for(pty=y;pty<(y+h);pty++){
    /* for each line, accumulate tints */
    contig_tinted=0;
    // note that end of for loop is ORIGINAL x+w, not adjusted
    for(ptx=scan_from_x;ptx<(x+w);ptx++){
      oval_line = 0;
      p_r = (UINT8*) &im->image32[pty][ptx];
      p_g = p_r + 1;
      p_b = p_r + 2;
      if (abs(*p_r - *p_g)>20 || abs(*p_g - *p_b)>20){
	contig_tinted++;
      }
      else {
	if (contig_tinted >= ow){
	  // when you end a long enough string of tinted pixels
	  oval_line = 1;
	  oval_start = ptx - contig_tinted;
	  //look ahead by oval height for another tinted pixel
	  //at approximately the oval's height and half the oval's width
	  p_r = (UINT8*) &im->image32[pty+oh][oval_start + (ow/2)];
	  p_g = p_r + 1;
	  p_b = p_r + 2;
	  if (abs(*p_r - *p_g)>20 || abs(*p_g - *p_b)>20){
	    //if found, look for at least one tinted pixel 
	    //on a line halfway down, from 1/2 ow before the oval_start 
	    //to the oval_start
	    //add this to oval list and increment y past the oval
	    oval_confirmed = 0;
	    for (ptx2 = oval_start - (ow/2);ptx2 < oval_start;ptx2++){
	      // confirm a tinted point halfway down 
	      // and preceding the upper oval line, 
	      // followed by an untinted point half oval width later
	      p_r = (UINT8*) &im->image32[pty+(oh/2)][ptx2];
	      p_g = p_r + 1;
	      p_b = p_r + 2;
	      p_r2 = (UINT8*) &im->image32[pty+(oh/2)][ptx2+(ow/2)];
	      p_g2 = p_r2 + 1;
	      p_b2 = p_r2 + 2;
	      if ( ((abs(*p_r - *p_g)>20 || abs(*p_g - *p_b)>20))
		   && (abs(*p_r2 - *p_g2)<20 && abs(*p_g2 - *p_b2)<20)){
		if ((*p_r2 > 224) && (*p_g2 > 224) && (*p_b2 > 224)){
		  oval_confirmed = 1;
		  oval_startx = ptx2;
		  break;
		}
	      }
	    }
	    //add ptx,pty to oval list
	    if(oval_confirmed){
	      item = Py_BuildValue("[ii]",oval_startx,pty);
	      PyList_Append(retlist,item);
	      //skip past this oval
	      pty += (oh + (oh/2));
	    }
	  }
	}
	contig_tinted = 0;
      }
    }
  }
  //repeat scan starting new bounding box oval's width after end of found ovals
  scan_from_x = oval_startx + ow + ow;
  }

  return retlist;
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject *
get_tinted_blobs(Imaging im, int x, int y, int w, int h, int testfuncarg )
{
  return getblobs_fromfunc(im,x,y,w,h,0,0,230, &is_tinted_by);
}


/* return a list with lengths of white/black stretches in pattern */
/* Hart ballots use I25 -- interleaved two of five, where two of every five
   bars or spaces are wide (Wikipedia). The first digit is encoded in bars,
   the second digit in spaces.  Start code is four narrows, nnnn; end code
   is WIDE, narrow, narrow -- Wnn.  
   Digt|Line width
   0	n	n	W	W	n
   1	W	n	n	n	W
   2	n	W	n	n	W
   3	W	W	n	n	n
   4	n	n	W	n	W
   5	W	n	W	n	n
   6	n	W	W	n	n
   7	n	n	n	W	W
   8	W	n	n	W	n
   9	n	W	n	W	n
*/


/* BALLOT ANALYSIS (works with RGB only) */
/* HART */
static inline PyObject*
getbarcode(Imaging im, int x, int y, int w, int h)
{
  UINT8 *p;
  int ptx, pty;
  int n;
  int sum;
  int avg;
  int group;
#define MAX_BW 50
  int blacks[MAX_BW];
  int whites[MAX_BW];
  int values[14];
  int numblacks=0;
  int numwhites=0;
  int whitethresh = 128;
  int lastwhite = 1;
  int whitecount = 0;
  int blackcount = 0;
  int intensity = 0;
  int firsttime = 1;
  /* if w is larger than h, we are dealing with vertically oriented bars; */
  /* else horizontally oriented bars */
  whitecount = 0;
  blackcount = 0;
  if (h>w){
    for(pty=(y+h);pty>=0;pty--){
      /* for each line, accumulate intensities, decide if white or black */
      intensity=0;
      for(ptx=x;ptx<(x+w);ptx++){
	p = (UINT8*) &im->image32[pty][ptx];
	intensity += (*p);
      }
      if ((intensity/w)>whitethresh) {
	/* it's white */
	if (lastwhite>0){
	  /* continuing white, increase white count */
	  whitecount++;
	}
	else {
	  /* new white, process blackcount */
	  blacks[numblacks++] = blackcount;
	  if (numblacks >= MAX_BW){
	    return NULL;
	  }
	  blackcount = 0;
	  whitecount = 1;
	  lastwhite = 1;
	}
      }
      else {
	/* it's black */
	if (lastwhite == 0){
	  /* continuing black, increase black count */
	  blackcount++;
	}
	else {
	  /* new black, process whitecount */
	  if (firsttime){
	    firsttime = 0;
	  }
	  else {
	    whites[numwhites++] = whitecount;
	    if (numwhites >= MAX_BW){
	      return NULL;
	    }
	  }
	  whitecount = 0;
	  blackcount = 1;
	  lastwhite = 0;
	}
      }
    }
  }
  else {
    for(ptx=(x+w);ptx<=x;ptx--){
      /* for each line, accumulate intensities, decide if white or black */
      intensity=0;
      for(pty=y;pty<(y+h);pty++){
	p = (UINT8*) &im->image32[pty][ptx];
	intensity += (*p);
      }
      if ((intensity/h)>whitethresh) {
	/* it's white */
	if (lastwhite>0){
	  /* continuing white, increase white count */
	  whitecount++;
	}
	else {
	  /* it's new white, process blackcount */
	  blacks[numblacks++] = blackcount;
	  if (numblacks >= MAX_BW){
	    return NULL;
	  }
	  blackcount = 0;
	  whitecount = 1;
	  lastwhite = 1;
	}
      }
      else {
	/* it's black */
	if (lastwhite == 0){
	  /* continuing black, increase black count */
	  blackcount++;
	}
	else {
	  /* it's new black, process whitecount */
	  if (firsttime){
	    firsttime=0;
	  }
	  else {
	    whites[numwhites++] = whitecount;
	    if (numwhites >= MAX_BW){
	      return NULL;
	    }
	  }
	  whitecount = 0;
	  blackcount = 1;
	  lastwhite = 0;
	}
      }
    }
  }
  /* now find out the average length of blacks and whites,
     and replace original lengths with 0 for narrow or 1 for wide */
  sum = 0;
  avg = 0;
  for (n=0;n<numblacks;n++){
    sum+= blacks[n];
  }
  avg = sum/numblacks;
  for (n=0;n<numblacks;n++){
    if (blacks[n]<=avg)blacks[n]=0;
    else blacks[n] = 1;
  }
  sum = 0;
  avg = 0;
  for (n=0;n<numwhites;n++){
    sum+= whites[n];
  }
  avg = sum/numwhites;
  for (n=0;n<numwhites;n++){
    if (whites[n]<=avg)whites[n]=0;
    else whites[n] = 1;
  }

  /* expect to find two narrow whites at the start along with two narrow
     blacks at the start; otherwise, complain */
  assert((whites[0]+whites[1]) == 0);
  assert((blacks[0]+blacks[1]) == 0);
  /* process seven groups of five from black, same from white
     for each group of five blacks and five whites, expect to find 
     two and only two wides; otherwise, complain */
  for (group=0;group<7;group++){
    int value;
    value = 0;
    if (blacks[2+(group*5)+0]>0)value += 1;
    if (blacks[2+(group*5)+1]>0)value += 2;
    if (blacks[2+(group*5)+2]>0)value += 4;
    if (blacks[2+(group*5)+3]>0)value += 7;
    if (value == 11) value = 0;
    values[group*2] = value;
    value = 0;
    if (whites[2+(group*5)+0]>0)value += 1;
    if (whites[2+(group*5)+1]>0)value += 2;
    if (whites[2+(group*5)+2]>0)value += 4;
    if (whites[2+(group*5)+3]>0)value += 7;
    if (value == 11) value = 0;
    values[(group*2)+1] = value;
  }
  return Py_BuildValue("ii", 
		       values[0]*1000000 + values[1]*100000 +
		       values[2]*10000 + values[3]*1000 +
		       values[4]*100 + values[5]*10 + values[6],
		       values[7]*1000000 + values[8]*100000 +
		       values[9]*10000 + values[10]*1000 +
		       values[11]*100 + values[12]*10 + values[13]
		       );

}

/* BALLOT ANALYSIS (works with RGB only) */
/* gather the average intensity of the specified region and four histo counts */
/* return None if not found, or a list with fifteen entries, five for each */
/* of the three color channels: */
/* avg intensity, count of pixels in 0-63, 64-127, 128-191, 192-255 */
/* the fine adjustments at the start are hart specific, and the call takes */
/* an extra parameter indicating whether to apply them */
static inline PyObject*
cropstats(Imaging im, int dpi, int gap, int x, int y, int w, int h, int fine_adj)
{
  UINT8 *p;
  UINT8 *p1;
  UINT8 *p2;
  UINT8 *p3;
  UINT8 *p4;
  int ptx, pty;
  int lowest[3], low[3], high[3], highest[3];
  unsigned int total[3], color[3];
  int count;
  int n;
  int thinline_width;
  int gap_width;
  int thickline_width;
  int thinstart_to_thickstart_width;
  int thickline_height;
  int one_fourth_height, three_fourths_height;
  int one_fourth_width, three_fourths_width;
  int found = 0;
  int suspicious = 0;
  PyObject * retlist;
  for (n=0;n<3;n++){
    total[n] = 0;
    color[n] = 0;
    lowest[n] = 0;
    low[n] = 0;
    high[n] = 0;
    highest[n] = 0;
  }
  count = w*h;


  /* step 1: fine adjust the x position
     for Hart Ballots at 150 dpi, we need to locate a vertical line
     of 2 pixels, move forward by 10 to 12 pixels to find a vertical line
     of 6 pixels, and back up one from the latter vertical line */
  thinline_width = dpi/75;
  thickline_width = dpi/25;
  gap_width = dpi/18;
  thinstart_to_thickstart_width = gap;
  thickline_height = dpi/6;
  found = 0;
  if (fine_adj != 0){
    // changing initial backup from dpi/6 to dpi/5,
    // because we'd been getting false positives on the first pass
    // before getting to do the second pass;
    // also added two extra pixel tests, and increased gap required intensity
    // from 192 to 208
    for (pty = y+(dpi/12); pty <= y+(dpi/10); pty++){
      for (ptx = x - (dpi/5);ptx < x+gap_width; ptx++){
	/* look for thinline */
	p1 = (UINT8*) &im->image32[y][ptx];
	p2 = (UINT8*) &im->image32[y][ptx+1];
	if ((*p1 < 192) && (*p2 < 192)){
	  // ptx may be the start of the fine line, is there a gap?
	  p1 = (UINT8*) &im->image32[y][ptx+(thinline_width*2)];
	  p2 = (UINT8*) &im->image32[y][ptx+(thinline_width*2)+1];
	  p3 = (UINT8*) &im->image32[y+2][ptx+(thinline_width*2)];
	  p4 = (UINT8*) &im->image32[y+2][ptx+(thinline_width*2)+1];
	  if ((*p1 > 208) && (*p2 > 208) && (*p3 > 208) && (*p4 > 208)){
	    // there's a gap; is there a thick line?
	    p1 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+1)];
	    p2 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+2)];
	    // and a thick line at the far side of the box?
	    p3 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+w-2)];
	    p4 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+w-4)];

	    if (((*p1 < 192) || (*p2 < 192)) && ((*p3 < 192) || (*p4 < 192))){
	      // the first x at which the intensity is low is the start of the box
	      x = ptx+(thinstart_to_thickstart_width);
	      found = 1;
	      break;
	    }
	    if (found) break;
	  }
	  if (found) break;
	}
	if (found) break;
      }
      if (found) break;
    }
    pty = y + (dpi/12);
    //if (found) printf("Adjusted x to %d\n",x);
    //else printf("No x adjustment from %d\n",x);
 
    // if not found after first pass, try wider adjustment
    if (found == 0){
      for (ptx = x - (dpi/3);ptx < x+gap_width; ptx++){
	/* look for thinline */
	p1 = (UINT8*) &im->image32[y][ptx];
	p2 = (UINT8*) &im->image32[y][ptx+1];
	if ((*p1 < 192) && (*p2 < 192)){
	  // ptx may be the start of the fine line, is there a gap?
	  p1 = (UINT8*) &im->image32[y][ptx+(thinline_width*2)];
	  p2 = (UINT8*) &im->image32[y][ptx+(thinline_width*2)+1];
	  p3 = (UINT8*) &im->image32[y+2][ptx+(thinline_width*2)];
	  p4 = (UINT8*) &im->image32[y+2][ptx+(thinline_width*2)+1];
	  if ((*p1 > 208) && (*p2 > 208) && (*p3 > 208) && (*p4 > 208)){
	    // there's a gap; is there a thick line?
	    p1 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+1)];
	    p2 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+2)];
	    // and a thick line at the far side of the box?
	    p3 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+w-2)];
	    p4 = (UINT8*) &im->image32[pty][ptx+(thinstart_to_thickstart_width+w-4)];

	    if (((*p1 < 192) || (*p2 < 192)) && ((*p3 < 192) || (*p4 < 192))){
	      // the first x at which the intensity is low is the start of the box
	      x = ptx+(thinstart_to_thickstart_width);
	      found = 1;
	      break;
	    }
	    if (found) break;
	  }
	  if (found) break;
	}
	if (found) break;
      }
    }

    /* step 2: fine adjust the y position
       for Hart Ballots at 150 dpi, the thick vertical line must 
       have a height of 23 or more pixels, and we should adjust the y
       to 12 above its center point */
    found = 0;
    for (pty = y - (dpi/8); pty < y + (dpi/10); pty++){
      p1 = (UINT8*) &im->image32[pty][x+1];
      p2 = (UINT8*) &im->image32[pty+1][x+1];
      if ((*p1 < 192) && (*p2 < 192)){
	// pty may be the start of the thick line, 
	// does it continue for (thickline_height-2)
	int counter;
	for (counter = 0;counter < (thickline_height * 2);counter++){
	  p1 = (UINT8*) &im->image32[pty+counter][x+2];
	  if (*p1 > 192) break;
	}
	if (counter > (thickline_height-2)){
	  if (counter % 2)counter--;
	  // if the mark is larger than the normal box,
	  // try to center on the mark instead of the box
	  y = pty + ((counter - thickline_height)/2) - 1;
	  found = 1;
	  break;
	}
	if (found) break;
      }
      if (found) break;
    }
  }

  for (pty = y; pty < (y+h); pty++) {
    for (ptx = x; ptx < (x+w); ptx++) {
      p = (UINT8*) &im->image32[pty][ptx];
      for (n=0;n<3;n++){
	color[n] = *(p+n);
	total[n] += p[n];
	switch ((color[n]>>6) & 3) 
	{
	case 0: 
	  lowest[n]++;
	  break;
	case 1:
	  low[n]++;
	  break;
	case 2:
	  high[n]++;
	  break;
	case 3:
	  highest[n]++;
	  break;
	}
      }
    }
  }
  one_fourth_height = h/4;
  three_fourths_height = (3*h)/4;
  one_fourth_width = w/4;
  three_fourths_width = (3*w)/4;
  suspicious = 0;
  for (pty = y+one_fourth_height; pty < (y+three_fourths_height); pty++) {
    for (ptx = x+one_fourth_width; ptx < (x+three_fourths_width); ptx++) {
      p = (UINT8*) &im->image32[pty][ptx];
      for (n=0;n<3;n++){
	if ( *(p+n) < 128 ){
	  suspicious = 1;
	  break;
	}
      }
    }
  }
  retlist = Py_BuildValue("iiiiiiiiiiiiiiiiii", 
			  total[0]/count, lowest[0],low[0],high[0],highest[0],
			  total[1]/count, lowest[1],low[1],high[1],highest[1],
			  total[2]/count, lowest[2],low[2],high[2],highest[2],
			  x,y, suspicious
			  );
  return retlist;
}


static PyObject* 
_thicken(ImagingObject* self, PyObject* args)
{
    PyObject* imOut;
    int xsize, ysize;
    if (!PyArg_ParseTuple(args, "ii", &xsize, &ysize))
        return NULL;

    imOut = PyImagingNew(
        ImagingThicken(self->image, xsize, ysize)
        );

    return imOut;
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getlines(ImagingObject* self, PyObject* args)
{
  int threshold;
  int allowed_misses;
  int ok;
  ok = PyArg_ParseTuple(args,"ii",&threshold,&allowed_misses);
  
  if (!ok) return NULL;
  
  return getlines(self->image, threshold, allowed_misses);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getgaps(ImagingObject* self, PyObject* args)
{
    PyObject* xy;
    int x, y;

    if (PyTuple_GET_SIZE(args) != 1) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be sequence of length 2"
            );
        return NULL;
    }

    xy = PyTuple_GET_ITEM(args, 0);

    if (_getxy(xy, &x, &y))
        return NULL;

    return getgaps(self->image, x, y, 0);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_gethgaps(ImagingObject* self, PyObject* args)
{
    PyObject* xy;
    int x, y;

    if (PyTuple_GET_SIZE(args) != 1) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be sequence of length 2"
            );
        return NULL;
    }

    xy = PyTuple_GET_ITEM(args, 0);

    if (_getxy(xy, &x, &y))
        return NULL;

    return getgaps(self->image, x, y, 1);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getfirstdark(ImagingObject* self, PyObject* args)
{
    int thresh = 0;
    int ok;

    if (PyTuple_GET_SIZE(args) != 1) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be an integer"
            );
        return NULL;
    }

    ok = PyArg_ParseTuple(args,"i",&thresh);

    if (!ok) return NULL;

    return getfirstdark(self->image, thresh);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getdarkextents(ImagingObject* self, PyObject* args)
{
  int x1, y1, x2, y2;
  int ok;

  if (PyTuple_GET_SIZE(args) != 4) {
    PyErr_SetString(
		    PyExc_TypeError,
		    "require 4 integer arguments (x1,y1,x2,y2)"
		    );
    return NULL;
  }
  
  ok = PyArg_ParseTuple(args,"iiii",&x1,&y1,&x2,&y2);

    if (!ok) return NULL;

    return getdarkextents(self->image, x1, y1, x2, y2);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getballotbrand(ImagingObject* self, PyObject * args)
{
  int dpi;
  int ok;
  if (PyTuple_GET_SIZE(args) != 1) {
    PyErr_SetString(
		    PyExc_TypeError,
		    "only one integer argument (DPI) accepted"
		    );
    return NULL;
  }
  ok = PyArg_ParseTuple(args,"i",&dpi);
  if (!ok) return NULL;
  return getballotbrand(self->image,dpi); 
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getbigglyphs(ImagingObject* self, PyObject * args)
{
  int minw,minh;
  int ok;
  if (PyTuple_GET_SIZE(args) != 2) {
    PyErr_SetString(
		    PyExc_TypeError,
		    "requires integer arguments minw, minh "
		    );
    return NULL;
  }
  ok = PyArg_ParseTuple(args,"ii",&minw,&minh);
  if (!ok) return NULL;
  return getbigglyphs(self->image,minw,minh); 
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getesstilt(ImagingObject* self, PyObject * args)
{
  int dpi;
  int ok;
  if (PyTuple_GET_SIZE(args) != 1) {
    PyErr_SetString(
		    PyExc_TypeError,
		    "only one integer argument (dpi) accepted"
		    );
    return NULL;
  }
  ok = PyArg_ParseTuple(args,"i",&dpi);
  if (!ok) return NULL;
  return getesstilt(self->image,dpi); 
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getessheadersandcodes(ImagingObject* self, PyObject * args)
{
  int dpi;
  int blocktype, blockx, blocky;
  int linediff;
  int ydiff;
  int ok;
  if (PyTuple_GET_SIZE(args) != 6) {
    PyErr_SetString(
		    PyExc_TypeError,
		    "six integers required (dpi, blocktype, blockx, blocky, linediff, ydiff)");
    return NULL;
  }
  ok = PyArg_ParseTuple(args,"iiiiii", 
			&dpi, 
			&blocktype, 
			&blockx, 
			&blocky, 
			&linediff,
			&ydiff);
  if (!ok) return NULL;
  return getessheadersandcodes(self->image,
				dpi,
				blocktype,
				blockx,
				blocky,
				linediff,
				ydiff); 
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getessheaderscodesovals(ImagingObject* self, PyObject * args)
{
  int dpi;
  int blocktype, blockx, blocky;
  int linediff;
  int ydiff;
  int ok;
  if (PyTuple_GET_SIZE(args) != 6) {
    PyErr_SetString(
		    PyExc_TypeError,
		    "six integers required (dpi, blocktype, blockx, blocky, linediff, ydiff)");
    return NULL;
  }
  ok = PyArg_ParseTuple(args,"iiiiii", 
			&dpi, 
			&blocktype, 
			&blockx, 
			&blocky, 
			&linediff,
			&ydiff);
  if (!ok) return NULL;
  return getessheaderscodesovals(self->image,
				dpi,
				blocktype,
				blockx,
				blocky,
				linediff,
				ydiff); 
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_gethartlandmarks(ImagingObject* self, PyObject* args)
{
    int dpi = 0;
    int need_vops = 1;
    int ok;

    if (PyTuple_GET_SIZE(args) != 2) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be an integer"
            );
        return NULL;
    }

    ok = PyArg_ParseTuple(args,"ii",&dpi,&need_vops);

    if (!ok) return NULL;

    return gethartlandmarks(self->image, dpi, need_vops);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getdieboldlandmarks(ImagingObject* self, PyObject* args)
{
    int dpi = 0;
    int need_vops = 1;
    int ok;

    if (PyTuple_GET_SIZE(args) != 2) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be an integer"
            );
        return NULL;
    }

    ok = PyArg_ParseTuple(args,"ii",&dpi,&need_vops);

    if (!ok) return NULL;

    return getdieboldlandmarks(self->image, dpi, need_vops);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getchanges(ImagingObject* self, PyObject* args)
{
    int xtop = 0;
    int xbottom = 0;
    int dpi = 0;
    int ok;

    if (PyTuple_GET_SIZE(args) != 3) {
        PyErr_SetString(
            PyExc_TypeError,
            "requires 3 integers (xtop, xbottom, dpi)"
            );
        return NULL;
    }

    ok = PyArg_ParseTuple(args,"iii",&xtop, &xbottom, &dpi);

    if (!ok) return NULL;

    return getchanges(self->image, xtop, xbottom, dpi);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_hasvdashes(ImagingObject* self, PyObject* args)
{
    int thresh = 0;
    int ok;

    if (PyTuple_GET_SIZE(args) != 1) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be an integer"
            );
        return NULL;
    }

    ok = PyArg_ParseTuple(args,"i",&thresh);

    if (!ok) return NULL;

    return hasvdashes(self->image, thresh);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_hashdashes(ImagingObject* self, PyObject* args)
{
    int thresh = 0;
    int ok;

    if (PyTuple_GET_SIZE(args) != 1) {
        PyErr_SetString(
            PyExc_TypeError,
            "argument 1 must be an integer"
            );
        return NULL;
    }

    ok = PyArg_ParseTuple(args,"i",&thresh);

    if (!ok) return NULL;

    return hashdashes(self->image, thresh);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getpotentialhlines(ImagingObject* self, PyObject* args)
{
  int startx, starty, dpi;
  int ok;
  ok = PyArg_ParseTuple(args,"iii",&startx,&starty,&dpi);
  if (!ok) return NULL;
  return getpotentialhlines(self->image, startx,starty,dpi);
   
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_gethartvoteboxes(ImagingObject* self, PyObject* args)
{
  int startx, starty, dpi;
  int ok;
  ok = PyArg_ParseTuple(args,"iii",&startx,&starty,&dpi);
  if (!ok) return NULL;
  return gethartvoteboxes(self->image, startx,starty,dpi);
   
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getdieboldvoteovals(ImagingObject* self, PyObject* args)
{
  int startx, starty, w,h,ow,oh;
  int ok;
  ok = PyArg_ParseTuple(args,"iiiiii",&startx,&starty,&w,&h,&ow,&oh);
  if (!ok) return NULL;
  return getdieboldvoteovals(self->image, startx,starty,w,h,ow,oh);
   
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getcolumnvlines(ImagingObject* self, PyObject* args)
{
  int startx, starty, endx;
  int ok;
  
  ok = PyArg_ParseTuple(args,"iii",&startx,&starty,&endx);
  
  if (!ok) return NULL;

  return getcolumnvlines(self->image, startx, starty, endx);
}


/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_getvdashes(ImagingObject* self, PyObject* args)
{
    int thresh = 0;
    int x1, y1, x2;
    int ok;

    ok = PyArg_ParseTuple(args,"iiii",&thresh,&x1,&y1,&x2);
    
    if (!ok) return NULL;

    return getvdashes(self->image, thresh, x1,y1,x2);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_gethdashes(ImagingObject* self, PyObject* args)
{
    int thresh = 0;
    int x1, y1, x2, y2;
    int ok;

    ok = PyArg_ParseTuple(args,"iiiii",&thresh,&x1,&y1,&x2,&y2);
    
    if (!ok) return NULL;

    return gethdashes(self->image, thresh, x1,y1,x2,y2);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject* 
_diebolddashcode(ImagingObject* self, PyObject* args)
{
    int thresh = 0;
    int dpi = 150;
    int starty = 0;
    int ok;

    ok = PyArg_ParseTuple(args,"iii",&thresh,&dpi, &starty);
    
    if (!ok) return NULL;

    return diebolddashcode(self->image, thresh, dpi, starty);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_cropstats(ImagingObject* self, PyObject* args)
{
  int dpi,gap,x,y,w,h,adj;
  int ok;
  ok = PyArg_ParseTuple(args,"iiiiiii",&dpi,&gap,&x,&y,&w,&h,&adj);
  
  if (!ok) return NULL;

  return cropstats(self->image, dpi , gap , x , y , w , h , adj);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getblobs(ImagingObject* self, PyObject* args)
{
  int x,y,w,h,tfa;
  int ok;
  ok = PyArg_ParseTuple(args,"iiiii",&x,&y,&w,&h,&tfa);
  
  if (!ok) return NULL;

  return getblobs(self->image, x,y,w,h,tfa);
}
/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getwideblobs(ImagingObject* self, PyObject* args)
{
  int x,y,w,h,minw,minh,tfa;
  int ok;
  ok = PyArg_ParseTuple(args,"iiiiiii",&x,&y,&w,&h,&minw,&minh,&tfa);
  
  if (!ok) return NULL;

  return getwideblobs(self->image, x,y,w,h,minw,minh,tfa);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_get_tinted_blobs(ImagingObject* self, PyObject* args)
{
  int x,y,w,h,tfa;
  int ok;
  ok = PyArg_ParseTuple(args,"iiiii",&x,&y,&w,&h,&tfa);
  
  if (!ok) return NULL;

  return get_tinted_blobs(self->image, x,y,w,h,tfa);
}

/* BALLOT ANALYSIS (works with RGB only) */
static PyObject*
_getbarcode(ImagingObject* self, PyObject* args)
{
  int x,y,w,h;
  int ok;
  ok = PyArg_ParseTuple(args,"iiii",&x,&y,&w,&h);
  
  if (!ok) return NULL;

  return getbarcode(self->image, x,y,w,h);
}


static PyMethodDef PilballotMethods[] = {
    {"thicken", (PyCFunction)_thicken, 1},
    {"getblobs", (PyCFunction)_getblobs, 1},
    {"getwideblobs", (PyCFunction)_getwideblobs, 1},
    {"get_tinted_blobs", (PyCFunction)_get_tinted_blobs, 1},
    {"getdieboldvoteovals", (PyCFunction)_getdieboldvoteovals, 1},
    {"getcolumnvlines", (PyCFunction)_getcolumnvlines, 1},
    {"gethartvoteboxes", (PyCFunction)_gethartvoteboxes, 1},
    {"getpotentialhlines", (PyCFunction)_getpotentialhlines, 1},
    {"getlines", (PyCFunction)_getlines, 1},
    {"getgaps", (PyCFunction)_getgaps, 1},
    {"gethgaps", (PyCFunction)_gethgaps, 1},
    {"getchanges", (PyCFunction)_getchanges, 1},
    {"getballotbrand", (PyCFunction)_getballotbrand, 1},
    {"getbigglyphs", (PyCFunction)_getbigglyphs, 1},
    {"getesstilt", (PyCFunction)_getesstilt, 1},
    {"getessheaderscodesovals", (PyCFunction)_getessheaderscodesovals, 1},
    {"getessheadersandcodes", (PyCFunction)_getessheadersandcodes, 1},
    {"gethartlandmarks", (PyCFunction)_gethartlandmarks, 2},
    {"getdieboldlandmarks", (PyCFunction)_getdieboldlandmarks, 1},
    {"getdarkextents", (PyCFunction)_getdarkextents, 1},
    {"getfirstdark", (PyCFunction)_getfirstdark, 1},
    {"hasvdashes", (PyCFunction)_hasvdashes, 1},
    {"getvdashes", (PyCFunction)_getvdashes, 1},
    {"hashdashes", (PyCFunction)_hashdashes, 1},
    {"gethdashes", (PyCFunction)_gethdashes, 1},
    {"getbarcode", (PyCFunction)_getbarcode, 1},
    {"diebolddashcode", (PyCFunction)_diebolddashcode, 1},
    {"cropstats", (PyCFunction)_cropstats, 1},
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
