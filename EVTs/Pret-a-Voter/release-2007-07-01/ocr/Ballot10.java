/* Constants to parameterise:

   16 transitions on the horizontal rows of the form (trans==2, trans==15)


*/


/* Experimental ballot-parsing software */

import java.util.*;  
import java.lang.Math;
import java.lang.String;
import javax.media.jai.JAI;
import javax.media.jai.RenderedOp;
import com.sun.media.jai.widget.DisplayJAI;
import javax.swing.JFrame;  
import javax.swing.JLabel;  
import javax.swing.JScrollPane;  
import javax.media.jai.PlanarImage;  
import java.awt.BorderLayout;  
import java.awt.Color;  
import java.awt.image.Raster;  
import java.awt.image.ColorModel;  
import java.awt.color.ColorSpace;  
import java.awt.image.BufferedImage;  
import java.awt.image.WritableRaster;  
import java.awt.Container;  
import java.awt.Graphics;  
import java.awt.event.MouseListener;
import java.awt.event.MouseEvent;
import javax.swing.event.MouseInputAdapter;
import java.awt.event.KeyListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyAdapter;


public class Ballot10 
{ 
  public static void main (String args[]) throws InterruptedException
  {
    if (args.length < 1) 
    {
        System.err.println ( "Usage: java Ballot10 image_file_name");
        System.exit(1);
    }

    final char [] hex = new char [] { '0', '1', '2', '3', '4', '5', '6', '7', 
                                      '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' };
    // Do we want debug output?
    final boolean debug = true;

    // Do we want graphical output?
    final boolean graphics = false;

    // Weights for the 7-segment bars
    final double [] weights = new double [] {4.0, -1.0, -1.0, 4.0};

    // Declare integer arrays for all of our template patterns, and read in 
    // the image files.

    /** tstyle=0 -> STV; tstyle=1 -> referendum */
    // final int [] tstyle = new int [] {0,0,0,0,0,1,1};
    final int [] tstyle = new int [] {0,0,1};

    final String [] [] tfile = { { "b6-blank.pgm", "b6-eight.pgm",
                                   "b6-one.pgm", "b6-oneone.pgm", 
                                   "b6-two.pgm", "b6-three.pgm",
                                   "b6-four.pgm", "b6-five.pgm",
                                   "b6-six.pgm"
                                 },
                                 { "b6-blcross.pgm", "b6-cross.pgm"
                                 }
                               };
    final int [] [] tval = { { -1, 8, 1, 1, 2, 3, 4, 5, 6 },  // chg in Ballot9
                             { -2, 1 }
                           };

    final int numStyles = tfile.length;

    Template templates[][] = new Template [numStyles][];
    // final int [] tPosition = new int [] { -1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0};
    // blank 7seg, blank cross, one, oneone, two, three, four, cross=1
    // need to pad with -99s?
    // final int [] tPosition = new int [] { -1, -2, 1, 1, 2, 3, 4, 1} ;

    // blank 7seg, blank cross, one, oneone, two, three, cross=1
    // final int [] tPosition = new int [] { -1, -2, 1, 1, 2, 3, 1} ;

    for (int style=0; style<numStyles; style++)
    { templates[style] =  new Template [tfile[style].length];
      for (int tCount=0; tCount<tfile[style].length; tCount++)
      {
        PlanarImage timage = JAI.create("fileload", tfile [style][tCount]); 
        BufferedImage tbi = timage.getAsBufferedImage();
        Raster tras = tbi.getData();
        ColorModel tcm = tbi.getColorModel();
        ColorSpace tcs = tcm.getColorSpace();
        int tminx = tbi.getMinX();
        int tminy = tbi.getMinY();
        int theight = tbi.getHeight();
        int twidth = tbi.getWidth();
        // System.err.println ("Template dimensions: "+ twidth + "x"+
                           // theight + " Bands:" + timage.getNumBands()); 
        int [][] template = new int [theight][twidth];

        // Convert each colour scheme into an 8-bit greyscale

        for (int yy=tminy; yy<tminy+theight; yy++)
        { for (int xx=tminx; xx<tminx+twidth; xx++)
          { double sum = 0;
            Color pixel = new Color (tbi.getRGB (xx,yy));
            float[] pixelrgb = new float[4];
            pixelrgb = pixel.getRGBColorComponents (pixelrgb);

            // System.err.print ("xxyy = " + xx + " " + yy + ";  pixel = " );
            for (int kk=0; kk<pixelrgb.length; kk++)
            { double dist = pixelrgb[kk]; 
              // System.err.print (dist + " ");
            sum += dist * dist;
            }
            // System.err.print (sum + " ");

            double d = Math.sqrt(sum) * 255.0 / Math.sqrt(3.0);
            template[yy][xx] = (new Long (Math.round(d))).intValue();
          }
        }
        templates[style][tCount] = new Template (template, tfile[style][tCount]);
      }
    }


    PlanarImage image = JAI.create("fileload", args[0]); 
    BufferedImage bi = image.getAsBufferedImage();
    Raster ras = bi.getData();
    ColorModel cm = bi.getColorModel();
    ColorSpace cs = cm.getColorSpace();
    int minx = bi.getMinX();
    int miny = bi.getMinY();
    int height = bi.getHeight();
    int width = bi.getWidth();
    String imageInfo = "Dimensions: "+ width + "x"+
                       height + " Bands:" + image.getNumBands();  
    if (debug) System.err.println (imageInfo);

    int [][] myimage = new int [height][width];

    int cvals = cm.getNumColorComponents();
    if (debug) System.err.println ("NumColorComponents = " + cvals);
    int[] colour = new int[cvals]; 


    // int cels = ras.getNumDataElements();
    // System.err.println ("getNumDataElements = " + cels);

    // float[] colourmin = new float[cvals]; 
    // float[] colourmax = new float[cvals]; 
    // float[] colourrange = new float[cvals]; 
    // for (int cc=0; cc<cvals; cc++)
    // { colourmin[cc] = cs.getMinValue(cc);
      // colourmax[cc] = cs.getMaxValue(cc);
      // colourrange[cc] = colourmax[cc] - colourmin[cc];
      // System.err.println ("color = " + colourmin[cc] + " -> " +  
                           // colourmax[cc] + " = " + colourrange[cc]);
    // }

    // For the full ballot form image, convert RGB etc to 8-bit greyscale
    // and collect a histogram for grey-level analysis

    int[] histogram = new int[256];     
    for (int yy=miny; yy<miny+height; yy++)
    { for (int xx=minx; xx<minx+width; xx++)
      { double sum = 0;
        Color pixel = new Color (bi.getRGB (xx,yy));
        float[] pixelrgb = new float[4];
        pixelrgb = pixel.getRGBColorComponents(pixelrgb);

        // System.err.print ("xxyy = " + xx + " " + yy + ";  pixel = " );
        for (int kk=0; kk<pixelrgb.length; kk++)
        { double dist = pixelrgb[kk]; 
          // System.err.print (dist + " ");
          sum += dist * dist;
        }
        // System.err.print (sum + " ");

        double d = Math.sqrt(sum) * 255.0 / Math.sqrt(3.0);
        int ind = (new Long (Math.round(d))).intValue();
        // System.err.println (ind + " ");
        histogram[ind] += 1;
        myimage[yy][xx] = ind;
      }
    }

    /*
    System.err.println ("Greyscale Histogram:");
    for (int kk=0; kk<histogram.length; kk++)
    { // System.err.println (kk + " " + histogram[kk] );
      System.err.print (histogram[kk] + " " );
    }
    System.err.println ();
    */

    int black = 0;
    int white = 255;

    int accum = 0;
    int index = 0;
    while (accum < (width*height*0.005))
    { accum += histogram[index];
      black = index;
      index ++;
    }

    index = 255;
    accum = width*height;
    while (accum < (width*height*0.99))  
    { accum += histogram[index];
      white = index;
      index --;
    }

    if (debug)
    { System.err.println ("Initial thresholds: black = " + black + 
                        "; white = " + white);
    }

    imageInfo = imageInfo + "   Initial thresholds: black = " + black + 
                                         "; white = " + white;

    // black = 190;
    // white = 200;

    // Set the black-white threshold half way between these.

    black = (black + white ) / 2;
    // black = (black + white + white + white) / 4;

    white = black;
    if (debug)
    { System.err.println ("Thresholds: black = " + black + 
                          "; white = " + white);
    }
    imageInfo = imageInfo + "   Final thresholds: black = " + black + 
                                         "; white = " + white;

    /*
    for (int kk=0; kk<256; kk++)
    { ras.getPixel(kk,kk,colour); 
      System.err.println ("kk = " + kk + ";  pixel = " + colour[0] + " " + 
                          colour[1] + " " + colour[2] + " " + colour[3]);
    }
    */

    // Create output display - using the same colour map as the original
    // image

    // See file:///opt/jdk1.5.0_05/docs/api/java/awt/GraphicsConfiguration.html
    // for information on determining the size of the screen, etc.

    WritableRaster wras = null;
    if (graphics)
    { wras = image.copyData();
    }

    DisplayJAI display;
    JFrame frame;
    Graphics graph;
    Container panel;

    if (graphics)
    { display = new DisplayJAI (new BufferedImage (cm, wras, false, null));
      frame = new JFrame("eVoting Ballot Scan");
      graph = display.getGraphics();
      frame.setTitle("DisplayJAI: "+args[0]);  

      panel = frame.getContentPane();
      panel.setLayout(new BorderLayout());  
      panel.add(new JScrollPane(display),BorderLayout.CENTER);
      panel.add(new JLabel(imageInfo),BorderLayout.NORTH);  

      MyMouseListener myMListener = new MyMouseListener();
      display.addMouseListener(myMListener);
      // display.addMouseMotionListener(myListener);

      MyKeyListener myKListener = new MyKeyListener();
      frame.addKeyListener(myKListener);

      frame.pack();
      frame.setVisible(true);
    }


    // Add white and black bars on left-hand edge of the right part of 
    // complete A4 scans [i.e. of un-split papers]

    if (height/width < 1.5)   // ~2.8 for RHS only
    { System.err.println ("Dealing with A4 form ... ");

      for (int hscan = (width*5)/100;
               hscan < (width*95)/100;
               hscan ++)
      { int dots = 0;
        int total = 0;
        int [] clr = new int[4];
        for (int vscan = (height*5)/100; 
               vscan < (height*95)/100;
               vscan++)
        { total++;
          if (myimage[vscan][hscan] < black) { dots ++; }
        }

        if (dots >= ((total * 98) / 100))
        { for (int vscan = 0; vscan < height; vscan++)
          { if (myimage[vscan][hscan] < black) 
            { myimage[vscan][hscan] = myimage[vscan][hscan-2] ;
              myimage[vscan][hscan-1] = myimage[vscan][hscan-2] ;
              if (graphics) 
              { wras.getPixel(hscan-2, vscan, clr);
                wras.setPixel(hscan-1, vscan, clr);
                wras.setPixel(hscan, vscan, clr);
              }
            }
          }
        }
      }

// while (width>10)
// {
// Thread.currentThread().sleep(5000);
// if (graphics) { frame.repaint(); }
// }


      // Draw vertical bar down centre of A4 page 
      // - emulate black background where perforations would be on narrow form

      for (int vscan = 0; 
               vscan < height;
               vscan++)
      { colour = new int[] {255,255,255,0};
        for (int hscan = (width*48)/100;
             hscan < (width*49)/100;
             hscan ++)
        { myimage[vscan][hscan] = 255;
          if (graphics) wras.setPixel(hscan, vscan, colour); 
        }

        colour = new int[] {0,0,0,0};
        for (int hscan = (width*49)/100;
                 hscan < (width*101)/200;
                 hscan ++)
        { myimage[vscan][hscan] = 0;
          if (graphics) wras.setPixel(hscan, vscan, colour); 
        }
      }
    }

    if (graphics) { frame.repaint(); }

    // Starting points
    int x1=10, y1=10, x2=width/20, y2=30;
    if (height/width < 1.5)   // ~2.8 for RHS only
    { x1=(width*49)/100;
      y1=10;
      x2=(width*55)/100;
      y2=30;
    }

    // Fill short (1 or 2 pixel) white runs in the leftmost black features
    // with black - i.e. fill in any perforation marks.

    for (int vscan = height*1/100; 
           vscan < height*99/100;
           vscan++)
    { // int blackness = myimage[vscan][9];
      for (int hscan = x1;
               hscan < x2;
               hscan ++)
      { if ((myimage[vscan][hscan] < black) && 
            (myimage[vscan][hscan+1] > black) && 
            (myimage[vscan][hscan+3] < black))
        { myimage[vscan][hscan+1] = 0;
        }
      }
    }


    /* Find initial points on black boundary */
    int pix = 0;
    while (x1<Math.min(width,height))
    { pix = myimage[y1][x1];          // wras.getPixel(ii, ii, colour);
      if (pix < black)  
      { colour = new int[] {255,0,255,0};
        if (graphics) { wras.setPixel(x1, y1, colour); }
        break;
      }
      x1++;
      y1++;
    }

    if (debug) System.err.println ("Initial point on LHS boundary: x1 = " + 
                                   x1 + "  y1 = " + y1);

    while (x2>0)
    { pix = myimage[y2][x2];          // wras.getPixel(ii, ii, colour);
      if (pix < black)  
      { colour = new int[] {255,0,255,0};
        if (graphics) { wras.setPixel(x2, y2, colour); }
        break;
      }
      x2--;
      y2++;
    }

    if (debug) System.err.println ("Initial point on LHS boundary: x2 = " + 
                                   x2 + "  y2 = " + y2);

    /* Floodfill the boundary - set it yellow */

    Pair topleft = new Pair (width/2, height/2);
    Pair bottomleft = new Pair (width/2, height/2);
    Pair topright = new Pair (width/2, height/2);
    Pair bottomright = new Pair (width/2, height/2);

    boolean [][] marks = new boolean [height+1][width+1];

    int cnt2 = floodfill (myimage, 
                          0, 0, width, height,
                          wras, true, black, true, 
                          new Pair (x1,y1),
                          new Pair (x2,y2),
                          new int[] {255,255,0,0}, 
                          topleft, bottomleft, 
                          topright, bottomright,
                          marks);


    if (debug) 
    { System.err.println ("Boundary count = " + cnt2);
      System.err.println ("Top left: " + topleft.x + ", " + topleft.y);
      System.err.println ("Top right: " + topright.x + ", " + topright.y);
      System.err.println ("Bottom left: " + bottomleft.x + ", " + 
                           bottomleft.y);
      System.err.println ("Bottom right: " + bottomright.x + ", " + 
                           bottomright.y);
    }

    if (graphics) { frame.repaint(); }

    // Look for white background and identify horizontal lines
    // Beware a grey or black stripe at the top and bottom of the scan.

    int lhs = 77;
    int rhs = 99;
    int lcount = 0;
    int t2sum = 0;
    int t15sum = 0;
    int prev = 0;
    int run = 0;
    final int numRaces2 = 3;  // move params below up above here

    for (int hscan = topleft.x + (topright.x - topleft.x)*5/1000; 
             hscan < (topleft.x + (topright.x - topleft.x)*800/1000); 
                                             // from 995
                                             // 800 allows for serial no. box
             hscan++)
    { int blackness = 0;
      int trans = 0;
      int t2 = 0;
      int t15 = 0;
      boolean dark = false;
      for (int vscan = topleft.y + (bottomleft.y - topleft.y)*5/1000;
               vscan < (topleft.y + (bottomleft.y - topleft.y)*995/1000);
               vscan++)
      { if (marks[vscan][hscan])   // checks flooded area
        { blackness ++;
          if (!dark) 
          { trans++; 
            if (trans == 2) { t2 = vscan; }
            if (trans == (numRaces2 * 2 + 1)) { t15 = vscan; }
            dark = true; 
          }
        }
        else
        { if (dark) 
          { trans++; 
            if (trans == 2) { t2 = vscan; }
            if (trans == (numRaces2 * 2 + 1)) { t15 = vscan; }
            dark = false; 
          }
        }
      }
      
      
      /*
        System.err.println ( "There were " + blackness +
                             " green pixels with " + trans + 
                             " transitions in column " + hscan + 
                             " t2=" + t2 + " t15=" + t15);
      */
        
      /*  Deal with scanner stripe - but too late  - moved up
      if (trans == 2)
      { System.err.println ( "There were " + blackness +
                             " green pixels with " + trans + 
                             " transitions in column " + hscan + 
                             " t2=" + t2 + " t15=" + t15);
        
        colour = new int[] {255,255,255,0};
        for (int vscan = topleft.y + (bottomleft.y - topleft.y)*5/1000;
                 vscan < (topleft.y + (bottomleft.y - topleft.y)*995/1000);
                 vscan++)
        { if ((myimage[vscan][hscan]<black) && 
                   !(myimage[vscan][hscan-1]<black)) 
          { //  marks[vscan][hscan] = false;
            myimage[vscan][hscan] = 255;
            if (graphics) wras.setPixel(hscan, vscan, colour); 
            System.err.println ( "reset (" + hscan + "," + vscan + ")" );
          }
        }
      }
      */

      if (trans == (numRaces2*2 + 2))
      { t2sum += t2;
        t15sum += t15;
        if (hscan == (prev + 1))
        { run++;
        }
        else
        { run = 0;
        }

        if (lcount == 0)
        { lhs = hscan;
        }
        else if (run > 10)
        { rhs = hscan;
        }

        lcount ++;
        prev = hscan;

        // System.err.println ( "trans16: " + hscan + " " + run + " " + rhs);
      }
    }
    
    if (graphics) frame.repaint();

    // FIXME - Exception in thread "main" 
    //         java.lang.ArithmeticException: / by zero
    //         at Ballot5.main(Ballot5.java:403)

    if (lcount == 0)
    { System.err.println ("lcount was zero - horizontal lines not found");
      System.err.println ("Expect failures below - form blank or inverted?");
      System.err.println ("Assuming form size parameters");
      lcount = 1;
      topleft = new Pair (61, 90);
      topright = new Pair (773, 90);
      bottomleft = new Pair (61, 3360);
      bottomright = new Pair (773, 3360);
    }
    else
    { topleft = new Pair (lhs, (t2sum + (lcount/2))/lcount);  // line 403
      topright = new Pair (rhs, (t2sum + (lcount/2))/lcount);
      bottomleft = new Pair (lhs, (t15sum + (lcount/2))/lcount);
      bottomright = new Pair (rhs, (t15sum + (lcount/2))/lcount);
    }


    if (debug)
    { System.err.println ("Central Section");
      System.err.println ("Top left: " + topleft.x + ", " + topleft.y);
      System.err.println ("Top right: " + topright.x + ", " + topright.y);
      System.err.println ("Bottom left: " + bottomleft.x + ", " + 
                           bottomleft.y);
      System.err.println ("Bottom right: " + bottomright.x + ", " + 
                           bottomright.y);
    }

    if (((topright.x - topleft.x) < 660) || 
        ((topright.x - topleft.x) > 750) ||
        ((bottomleft.y - topleft.y) < 3100) ||
        ((bottomleft.y - topleft.y) > 3400) )
    {
      System.err.println ("69,0,00000000000,0,0,0,0,0,0,0,Central Section is wrong size," + args[0] + ",,,,,,");
      System.out.println ("69,0,00000000000,0,0,0,0,0,0,0,Central Section is wrong size," + args[0] + ",,,,,,");
      System.exit(1);
    }


    /* Set corners red */
    colour = new int[] {255,0,0,0};
    if (graphics)
    { wras.setPixel(topleft.x, topleft.y, colour);
      wras.setPixel(topleft.x+1, topleft.y+1, colour);
      wras.setPixel(topleft.x+2, topleft.y+2, colour);

      wras.setPixel(topright.x, topright.y, colour);
      wras.setPixel(topright.x-1, topright.y+1, colour);
      wras.setPixel(topright.x-2, topright.y+2, colour);

      wras.setPixel(bottomleft.x, bottomleft.y, colour);
      wras.setPixel(bottomleft.x+1, bottomleft.y-1, colour);
      wras.setPixel(bottomleft.x+2, bottomleft.y-2, colour);

      wras.setPixel(bottomright.x, bottomright.y, colour);
      wras.setPixel(bottomright.x-1, bottomright.y-1, colour);
      wras.setPixel(bottomright.x-2, bottomright.y-2, colour);

      frame.repaint();
    }




    /* Ballot form parameters - version 1 (8/12/06) 
    // these offsets now measured from INSIDE of any border 
    //   (these measurements are from the outside)
    final double xoff = 0.372;
    final double [][] yoff = new double[][] 
       { {0.050, 0.070, 0.091, 0.113, 0.134, 0.157, 0.179, 0.045, 0.183}
       };
    final int numRaces = yoff.length;    // 1
    final double [] boxLine = { 1.007 };   

    final double [][] bar = {  // minx,miny,maxx,maxy ordering
                              { 0.26, 0.06, 0.67, 0.17 },
                              { 0.20, 0.12, 0.33, 0.47 },
                              { 0.60, 0.11, 0.72, 0.49 },
                              { 0.24, 0.43, 0.64, 0.56 },
                              { 0.17, 0.51, 0.28, 0.90 },
                              { 0.55, 0.52, 0.71, 0.90 },
                              { 0.18, 0.82, 0.61, 0.93 }
                            };
    */

    //---------------------------------------------------------------------
    //---------------------------------------------------------------------

    /* Ballot form parameters - versions 2  + 3  (2/2/07) 

    // no. of pixels in line surrounding mark boxes as ratio of whole mark box
    final double [] boxLine = { 1.013, 1.007, 1.017 };   
    final double cellInnerRatio = 1.16;

    // Offsets from reference frame to mark boxes
    final double xoff = 0.080;
    final double [][] yoff = new double[][] 
     { {0.0745, 0.1157, 0.1569, 0.1982, 0.0951, 0.2188},
       {0.3700, 0.4112, 0.4524, 0.4937, 0.5349, 0.5761, 0.6173, 0.3906, 0.6379},
       {0.7831, 0.8243, 0.8655, 0.8037, 0.8861}
     };
    final int numRaces = yoff.length;    // 3

    final double [][] bar = {  // minx,miny,maxx,maxy ordering
                              { 0.35, 0.05, 0.69, 0.16 },
                              { 0.24, 0.16, 0.35, 0.36 },
                              { 0.69, 0.16, 0.80, 0.36 },
                              { 0.33, 0.41, 0.65, 0.51 },
                              { 0.19, 0.53, 0.31, 0.75 },
                              { 0.62, 0.53, 0.75, 0.75 },
                              { 0.31, 0.76, 0.61, 0.90 }
                            };
    */

    //---------------------------------------------------------------------
    //---------------------------------------------------------------------

    /* Ballot form parameters - version 4/5 (12/2/07) 

    final double cellInnerRatio = 1.09;

    // Offsets from reference frame to mark boxes
    final double xoff = 0.13;
    final double [][] yoff = new double[][] 
     { {0.012, 0.055, 0.096, 0.034, 0.117},
       {0.167, 0.209, 0.250, 0.292, 0.188, 0.313},
       {0.366, 0.407, 0.450, 0.387, 0.471},
       {0.522, 0.563, 0.543, 0.584},
       {0.642, 0.683, 0.663, 0.704},
       {0.761, 0.802, 0.782, 0.823},
       {0.880, 0.921, 0.901, 0.942}
     };
    final int numRaces = yoff.length;    

    final int [] style = new int [] {0,0,0,0,0,1,1};

    final double [] baroff = new double [] {1.04, 1.66};    // barcode 
    final int bcodeWidth = 24;
    final int bcodeHeight = 64;
    */


    //---------------------------------------------------------------------
    //---------------------------------------------------------------------

    /* Ballot form parameters - versions 6 & 7 & 8 (23/2/07)

    final double cellInnerRatio = 1.102;
    final int wobbleDist = 5;

    // Offsets from reference frame to mark boxes
    final double xoff = 0.123;
    final double [][] yoff = new double[][] 
     { {0.020, 0.061, 0.103, 0.040, 0.123},
       {0.192, 0.234, 0.212, 0.254},
       {0.323, 0.364, 0.407, 0.343, 0.427},
       {0.496, 0.537, 0.516, 0.557},
       {0.627, 0.668, 0.647, 0.688},
       {0.757, 0.800, 0.777, 0.820},
       {0.889, 0.930, 0.909, 0.950}
     };
    final int numRaces = yoff.length;    

    final int [][] mbox = new int [][]
      // { {1280,160,1433,566},
        // {1280,735,1433,1000},
        // {1280,1166,1433,1569},
        // {1280,1733,1433,2001},
        // {1280,2166,1433,2429},
        // {1280,2596,1433,2855},
        // {1280,3020,1433,3287}
      // };
      { {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5}
      };



    final double [] baroff = new double [] {1.04, 1.66};    // barcode 
    final int bcodeWidth = 24;
    final int bcodeHeight = 64;

    */

    //---------------------------------------------------------------------
    //---------------------------------------------------------------------

    /* Ballot form parameters - version 9 (8/5/07) */

    final double cellInnerRatio = 1.102;
    final int wobbleDist = 5;

    // Offsets from reference frame to mark boxes
    final double xoff = 0.102;     // 0.160;
    final double [][] yoff = new double[][] 
     { {0.069, 0.115, 0.158, 0.200, 0.247, 0.090, 0.268},
       {0.436, 0.483, 0.525, 0.568, 0.611, 0.654, 0.457, 0.675},
       {0.847, 0.889, 0.868, 0.910}
     };
    final int numRaces = yoff.length;    

    final int [][] mbox = new int [][]
      /*
      { {1280,160,1433,566},
        {1280,735,1433,1000},
        {1280,1166,1433,1569},
        {1280,1733,1433,2001},
        {1280,2166,1433,2429},
        {1280,2596,1433,2855},
        {1280,3020,1433,3287}
      };
      */
      { {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5},
        {5,5,width-5,height-5}
      };



    final double [] baroff = new double [] /* {0.64, 1.00};*/  {1.053, 1.635};    // barcode 
    final int bcodeWidth = 24;
    final int bcodeHeight = 64;

    int raceErrors = 0;
    int resultCode = 0;
    String signedHash = new String ("");
    String [] raceResult = new String [numRaces] ;
    String [] raceMessage = new String [numRaces] ;

    // Iterate over the races on this ballot form
    for (int thisRace=0; thisRace<numRaces; thisRace++)
    { raceResult[thisRace] = "";
      raceMessage[thisRace] = "";

      if (debug) System.err.println ("Race " + thisRace);

      Pair [] points = new Pair[yoff[thisRace].length] ;
      final int numCands = yoff[thisRace].length - 2;
      final double dnumCands = (double) numCands;

      for (int ii=0; ii<yoff[thisRace].length; ii++)
      { points[ii] = new Pair ((topleft.x+bottomleft.x)/2 +
        ((bottomright.x+topright.x)-(topleft.x+bottomleft.x))/2*xoff,  
        (topleft.y+topright.y)/2 +
        ((bottomleft.y+bottomright.y)-(topleft.y+topright.y))/2 
                           *yoff[thisRace][ii]);

        if (graphics) { wras.setPixel(points[ii].x, points[ii].y, colour); }
        // System.err.println ("point" + ii + ": " + points[ii].x + ", " +
                            // points[ii].y);
      }


      /* Set whole number box blue */
      Pair numtopleft = new Pair ();
      Pair numbottomleft = new Pair ();
      Pair numtopright = new Pair ();
      Pair numbottomright = new Pair ();
      int cnt = floodfill (myimage, 
                            // should be box environs only
                            // 30, 170, 220 ,630,
                            0,0,width,height,
                            // mbox[thisRace][0]-5,
                            // mbox[thisRace][1]-5,
                            // mbox[thisRace][2]+5,
                            // mbox[thisRace][3]+5,
                           wras, true, white, false, 
                           points[yoff[thisRace].length-2], 
                           points[yoff[thisRace].length-1], 
                            new int[] {0,0,255,0}, 
                            numtopleft, numbottomleft, 
                            numtopright, numbottomright,
                            marks);

      
      System.err.println ("Mark box count = " + cnt);
      System.err.println ("race " + thisRace + ": mark box: " + 
                          numtopleft.x + ", " + numtopleft.y);
      System.err.println ("race " + thisRace + ": mark box: " + 
                          numbottomleft.x + ", " + numbottomleft.y);
      System.err.println ("race " + thisRace + ": mark box: " + 
                          numtopright.x + ", " + numtopright.y);
      System.err.println ("race " + thisRace + ": mark box: " + 
                          numbottomright.x + ", " + numbottomright.y);
      


      Pair a = new Pair (0,0);
      Pair b = new Pair (0,0);
      Pair c = new Pair (0,0);
      Pair d = new Pair (0,0);

      int digitFound [] = new int [10];  // no. of times each rank digit is seen
      int candidate [] = new int [10];   // defensive - only need 1-numCands 
      int rank [] = new int[10];         // user might write any digit

      // Iterate over the candidate rankings for this race
      for (int cell=0; cell<numCands; cell++)
      {
        if (debug) System.err.println ("  cell " + cell);

        int cellInnerWidth = ((numtopright.x + numbottomright.x) - 
                         (numtopleft.x + numbottomleft.x))/2 +1 ;

        double ch = cellInnerRatio * cellInnerWidth ;

        int cellInnerHeight = (new Long (Math.round(ch))).intValue();

        double margin = ((((numbottomleft.y + numbottomright.y) -
                            (numtopleft.y + numtopright.y)) * 0.5 ) - 
                                             ch*dnumCands) / (dnumCands-1.0);

        if ((cellInnerWidth < 110) ||
            (cellInnerWidth > 130) ||
            (cellInnerHeight < 120) ||
            (cellInnerHeight > 140) )
        { 
          System.err.println ("68,0,00000000000,0,0,0,0,0,0,0,Cell is wrong size," + args[0] + ",,,,,,");
          System.out.println ("68,0,00000000000,0,0,0,0,0,0,0,Cell is wrong size," + args[0] + ",,,,,,");

/*
while (true)
{
Thread.currentThread().sleep(1000);
if (graphics) { frame.repaint(); }
}
*/

          System.exit(1);
        }

        Pair coord = new Pair (
          numtopleft.x,                     //+ if rotated?
          numtopleft.y + (ch+margin)*cell ); //+ if rotated?

        // System.err.println ("  Top Left of cell " + cell + " is (" + 
                          // coord.x +", " + coord.y + "); width = " +
                          // cellInnerWidth + "  height = " + cellInnerHeight);


        // assumes that all template boxes are the same size
        final int templHeight = templates[0][0].height;
        final int templWidth = templates[0][0].width;
        // System.err.println ("  templHeight, Width = " + templHeight + " " +
                            // templWidth);

      colour = new int[] {255,0,255,0};

      int wX = 0;
      int wY = 0;
      double wQual = 999999.0;
      for (int wobbleY=-wobbleDist; wobbleY<wobbleDist; wobbleY++)
      { for (int wobbleX=-wobbleDist; wobbleX<wobbleDist; wobbleX++)
        { 
          double qual = 0.0;
          for (int row=0; row<cellInnerHeight; row++)
          { 
            int ty = (row + wobbleY) * templHeight / cellInnerHeight;
            for (int col=0; col<cellInnerWidth; col++)
            { 
              int tx = (col + wobbleX) * templWidth / cellInnerWidth;

              /*
              if (template[ty][tx] < black)
              { wras.setPixel (coord.x + row, coord.y + col, colour);
              }
              */

              int q = 0;
              if (tx>=0 && tx<templWidth && ty>=0 && ty<templHeight)
              // FIXME - Exception in thread "main" 
              //         java.lang.ArrayIndexOutOfBoundsException: 1304
              //         at Ballot5.main(Ballot5.java:631)

              // line 631 immediately below here
              { q = templates[tstyle[thisRace]][0].template[ty][tx] -
                                 myimage[coord.y + row][coord.x + col] ;
              }
              else
              { q = 255 - myimage[coord.y + row][coord.x + col] ;
              }
              qual += q*q;
            }
          } 

          qual = Math.sqrt(qual);
          // System.err.println ("  Quality = " + wobbleX + " " + 
                                  // wobbleY + " " + qual);

          if (qual < wQual)
          { wX = wobbleX;
            wY = wobbleY;
            wQual = qual;
          }

        } // end wobbleX
      } // end wobbleY

      if (debug) System.err.println ("  Chosen wobble factor: quality = " + 
                                      wQual + " @ "+ wX + ", " + wY);


      int [][] rect = new int[cellInnerHeight][cellInnerWidth];
      int [][] extra = new int[cellInnerHeight][cellInnerWidth];

      for (int row=0; row<cellInnerHeight; row++)
      { for (int col=0; col<cellInnerWidth; col++)
        { int pixel = myimage[coord.y + row][coord.x + col];
          rect[row][col] = pixel;
          extra[row][col] = -1;
        }
      }

      // Thicken characters drawn
      final int thicken = 2;
      for (int row=thicken; row<cellInnerHeight-thicken; row++)
      { for (int col=thicken; col<cellInnerWidth-thicken; col++)
        { int pixel = rect[row][col];
          for (int oy=-thicken; oy<=thicken; oy++)
          { for (int ox=-thicken; ox<=thicken; ox++)
            { if ((pixel < black) && (rect[row+oy][col+ox] > white))
              { extra[row+oy][col+ox] ++;
              }
            }
          }
        }
      }

      int [] colour2 = new int[4];
      for (int row=1; row<cellInnerHeight-1; row++)
      { for (int col=1; col<cellInnerWidth-1; col++)
        { if ( extra[row][col] > 0)
          { rect[row][col] = 0;
          }
            colour2[0] = rect[row][col];
            colour2[1] = rect[row][col];
            colour2[2] = rect[row][col];
            // wras.setPixel (coord.x + col + 200, coord.y + row, colour2);
        }
      }

      // System.err.println ("  Thinning fragmented pixels:");
      int count = 1;
      boolean odd = false;   // carefully chosen
      while (count > 0)
      { // System.err.print ("Count was " + count + "  ");
        count = 0;
        odd = !odd;
        for (int row=1; row<cellInnerHeight-1; row++)
        { for (int col=1; col<cellInnerWidth-1; col++)
          { int bb = 0;
            int ww = 0;
            for (int oy=-1; oy<=1; oy++)
            { for (int ox=-1; ox<=1; ox++)
              { if (rect[row+oy][col+ox] < black)
                { if (rect[row][col] < black) { bb++; }
                }
                else
                { if (rect[row][col] > white) { ww++; }
                }
              }
            }
            if (odd && bb <= 3  && rect[row][col] < black)
            { rect[row][col] = 255;
              count ++;
            }
            if (!odd && ww <= 3 && rect[row][col] > white)
            { rect[row][col] = 0;
              count ++;
            }
          }
        }
      }

      // System.err.println ();
      // System.err.println ("  Comparing using carefully-positioned templates:");


      int [] order = new int [templates[tstyle[thisRace]].length];
      double [] value = new double [templates[tstyle[thisRace]].length];
      for (int plate=0; plate<templates[tstyle[thisRace]].length; plate++)
      {
        int templCount = 0;
        double imageCount = 0.0;
        int [][] template = templates[tstyle[thisRace]][plate].template;
        int [][] mask = templates[tstyle[thisRace]][1].template;

        for (int row=0; row<cellInnerHeight; row++)
        { 
          int ty = (row + wY) * templHeight / cellInnerHeight; 
          for (int col=0; col<cellInnerWidth; col++)
          { 
            int tx = (col + wX) * templWidth / cellInnerWidth;

            int pixel = myimage[coord.y + row][coord.x + col];

            if (graphics)
            { wras.getPixel (coord.x + col, coord.y + row, colour2);
            }

            // Check within template
            if (tx>=0 && tx<templWidth && ty>=0 && ty<templHeight)
            { if (mask[ty][tx] < black)
              { if (template[ty][tx] < black)
                { templCount ++;
                  if (pixel < black)
                  { imageCount += weights[0];
                    if (false && graphics)
                    { wras.setPixel (coord.x + col + 130*(plate+1), coord.y + row, 
                                     new int[] {255,0,255,0});
                    }
                  }
                  else
                  { imageCount += weights[1];
                    if (false && graphics)
                    { wras.setPixel (coord.x + col + 130*(plate+1), coord.y + row, 
                                     new int[] {255,0,0,0});
                    }
                  }
                }
                else
                { if (pixel < black)
                  { imageCount += weights[2];     // How much less??
                    if (false && graphics)
                    { wras.setPixel (coord.x + col + 130*(plate+1), coord.y + row, 
                                     new int[] {0,0,255,0});
                    }
                  }
                  else
                  { imageCount += weights[3];
                    if (false && graphics)
                    { wras.setPixel (coord.x + col + 130*(plate+1), coord.y + row, 
                                     new int[] {0,0,0,0});
                    }
                  }
                }
              }
              else
              { // don't count marks outside the dashed 7-segment area
                if (false && graphics)
                { wras.setPixel (coord.x + col + 130*(plate+1), coord.y + row, 
                                 new int[] {0,255,0,0});
                }
              }
            }
            else
            { // assume border of cell is white - no counts.
              if (false && graphics)
              { wras.setPixel (coord.x + col + 130*(plate+1), coord.y + row, 
                               new int[] {127,127,127,0});
              }
            }
          }
        }

        order[plate] = plate;
        if (templCount > 0)
        { value[plate] = imageCount;  // * 100.0 / templCount; 
        }
        else
        { value[plate] = -1000;   // how was this chosen? -10 normalised to 100
        }

        // System.err.println ("  Template " + plate + "('" + 
           // templates[tstyle[thisRace]][plate].filename + "'): hit rate = " +
           // value[plate]);

      }  // end of for (plate)

      // bubble sort - easier than setting up Arrays.sort()?
      for (int p1=0; p1<order.length; p1++)
      { for (int p2=p1; p2<order.length; p2++)
        { if (value[order[p1]] < value[order[p2]])
          { int o = order[p1];
            order[p1] = order[p2];
            order[p2] = o;
          }
        }
      }

      int indx = 0;
      // while (value[order[indx]] >= value[order[0]] * 0.60)
      while (indx < order.length)
      { if (debug) System.err.println ("  Template " + order[indx] + " ('" + 
                         templates[tstyle[thisRace]][order[indx]].filename + 
                         "'): hit rate = " +
                         value[order[indx]]);
        indx++;
      }

      // best result is order[0]

      if (graphics)
      { for (int row=0; row<cellInnerHeight; row++)
        { for (int col=0; col<cellInnerWidth; col++)
          { colour2[0] = rect[row][col];
            colour2[1] = rect[row][col];
            colour2[2] = rect[row][col];
            // wras.setPixel (coord.x + col + 400, coord.y + row, colour2);
          }
        }
      }


      /* Colour bar test
      for (int playX=0; playX<256; playX++)
      { colour2[0] = playX;
        colour2[1] = playX;
        colour2[2] = playX;
        for (int playY=0; playY<10; playY++)
        {
          wras.setPixel (coord.x + playX + playX, 
                         coord.y + playY + 20, colour2);
          wras.setPixel (coord.x + playX + playX + 1, 
                         coord.y + playY + 20, colour2);
        }
      }
      */



        // best result is indexed in order[0]
        candidate[cell] = tval[tstyle[thisRace]][order[0]];


        if (candidate[cell] > 0)
        { if (debug) System.err.println ("  Cell " + cell + 
                               " is marked for candidate ranked " + 
                               candidate[cell]);
          digitFound[candidate[cell]] ++;
          rank[candidate[cell]] = cell;
          if (tstyle[thisRace] == 0)
          { raceResult[thisRace] += candidate[cell];
          }
          else if (tstyle[thisRace] == 1)
          { raceResult[thisRace] += "x";
          }
        }
        else if (candidate[cell] == 0)
        { if (debug) System.err.println ("  Cell " + cell + 
                                         " is a zero [illegal value]");
          digitFound[candidate[cell]] ++;
          rank[candidate[cell]] = cell;
          raceResult[thisRace] += "?";
        }
        else  // if (candidate[cell] < 0)
        { if (debug) System.err.println ("  Cell " + cell + 
                                         " is blank or was not recognised");
          if (tstyle[thisRace] == 0)
          { raceResult[thisRace] += "-"; 
          }
          else if (tstyle[thisRace] == 1)
          { raceResult[thisRace] += "o"; 
          }
          else
          { raceResult[thisRace] += "a";
          }
        }

        // System.err.println ();
      }   // end cell  

      // Are these Strings now??

      // Check for omitted rankings (9 downwards)
      int highestPos = 9;
      for (int jjj=9; jjj>=0; jjj--)
      { if (digitFound[jjj] == 0)
        { highestPos = jjj-1;
        }
        else
        { highestPos = jjj;
          break;
        }
      }

      // Check that all lowest ranks have been supplied
      boolean error = false;
      for (int jjj=highestPos; jjj >= 1; jjj--)
      { if (digitFound[jjj] == 0)
        { if (debug) System.err.println ("Rank number " + jjj + 
                              " does not appear in this race");
          error = true;
          raceMessage [thisRace] = "Number " + jjj + " does not appear";
        }
        if (digitFound[jjj] > 1)
        { if (debug) System.err.println ("Rank number " + jjj + 
                              " appears too often (" + digitFound[jjj] +
                              " times) in this race");
          error = true;
          raceMessage [thisRace] = "Number " + jjj + " appears more than once";
        }
      }

      final String [] order = {"1st", "2nd", "3rd", "4th", "5th", 
                               "6th", "7th", "8th", "9th", "10th"};
      // Final report for this race
      if (error)
      { if (debug) System.err.println ("Race " + thisRace + 
                                       ": errors found in this race");
        raceErrors ++; 
      }
      else if (highestPos < 0)
      { if (debug) System.err.println ("Race " + thisRace + ": no marks found");
        // raceErrors ++; 
        // raceMessage [thisRace] = "Race " + thisRace + ": no marks found"
      }
      else
      { if (debug) System.err.println ("Race " + thisRace + 
                             " recorded successfully; the rankings are: " );
        for (int jjj=1; jjj<=highestPos; jjj++)
        { // ranks start at 0
          if (debug) System.err.println (order[jjj-1] + ": candidate no. " + 
                                         (int)(rank[jjj]+1) );  
        }
      }
      if (debug) System.err.println ();

    }  // end of thisRace loop

    if (graphics) { frame.repaint(); }

    /* Set whole barcode box blue */
    Pair bcodetopleft = new Pair ();
    Pair bcodebottomleft = new Pair ();
    Pair bcodetopright = new Pair ();
    Pair bcodebottomright = new Pair ();
    int cnt4 = floodfill (myimage,
                         // should be box environs only
                         // 30, 170, 220 ,630,
                         0,0,width,height,
                         wras, true, black, true,
                         new Pair ((topleft.x+bottomleft.x)/2 +
                                 ((bottomright.x+topright.x)-
                                  (topleft.x+bottomleft.x))/2*baroff[0], 
                                  270 /*125*/),   //FIXME  points[0].y),
                         new Pair ((topleft.x+bottomleft.x)/2 +
                                 ((bottomright.x+topright.x)-
                                  (topleft.x+bottomleft.x))/2*baroff[1], 
                                  1350  /*1200*/),    // FIXME points[1].y),
                         new int[] {0,0,255,0}, 
                         bcodetopleft, bcodebottomleft,
                         bcodetopright, bcodebottomright,
                         marks);


    // Process barcode here

    // outer width (height) of barcode box / width (height) of one pixel
    double hbit = ((bcodetopright.x-bcodetopleft.x) / 25.3  /*25.049*/);
    double vbit = ((bcodebottomleft.y-bcodetopleft.y) / 65.3 /*65.04*/);
    if (debug) System.err.println ("Barcode bits are " +
                                    hbit + " pixels across and " +
                                    vbit + " pixels down");

    // Bias frame to 

    if (debug)
    {
      System.err.println ("Barcode boundary count = " + cnt4);
      System.err.println ("Top left: " + bcodetopleft.x + ", " + 
                           bcodetopleft.y);
      System.err.println ("Top right: " + bcodetopright.x + ", " + 
                           bcodetopright.y);
      System.err.println ("Bottom left: " + bcodebottomleft.x + ", " + 
                           bcodebottomleft.y);
      System.err.println ("Bottom right: " + bcodebottomright.x + ", " + 
                           bcodebottomright.y);
    }

    if (graphics)
    { wras.setPixel (bcodetopleft.x, bcodetopleft.y, new int[] {255,0,0,0});
      wras.setPixel (bcodetopright.x, bcodetopright.y, new int[] {255,0,0,0});
      wras.setPixel (bcodebottomleft.x, bcodebottomleft.y, new int[] {255,0,0,0});
      wras.setPixel (bcodebottomright.x, bcodebottomright.y, new int[] {255,0,0,0});
    }


    // System.err.print ("bar: ");
    for (int brow=0; brow < bcodeHeight; brow++)
    { double vpos = bcodetopleft.y + 
            ((double)(bcodebottomleft.y-bcodetopleft.y))/(bcodeHeight+1.4) * 
                                                                 (1.2 + brow);
      int [] rowbits = new int [bcodeWidth];
      for (int bcol=0; bcol<bcodeWidth; bcol++)
      { double hpos = bcodetopleft.x +
            ((double)(bcodetopright.x-bcodetopleft.x))/(bcodeWidth+1.4) * 
                                                                (1.2 +bcol);
        int vposi = (new Long (Math.round(vpos+(((bcodetopright.y-bcodetopleft.y)*bcol)/bcodeWidth)+0.5))).intValue();
        int hposi = (new Long (Math.round(hpos+(((bcodebottomleft.x-bcodetopleft.x)*brow)/bcodeHeight)+0.5))).intValue();
        // System.err.println (hposi + " " + vposi + " " ); 
        // System.err.println (bcodetopright.y + " " + bcodetopleft.y + " " +
               // bcodebottomleft.x + "  " + bcodetopleft.x + " " + 
               // brow + " " + bcol );
        int sample = 0;
        for (int vposii=vposi-1; vposii<=vposi+1; vposii++)
        { for (int hposii=hposi-1; hposii<=hposi+1; hposii++)
          { sample += myimage[vposii][hposii];
            if (graphics) 
            { int [] colr = new int[4] ;
              wras.getPixel (hposii, vposii, colr);
              wras.setPixel (hposii, vposii, new int[] {255-colr[0],
                                                      255-colr[1],
                                                      255-colr[2],
                                                      colr[3]}); 
            }
          }
        }

        if ((sample/9) < black)
        { if (debug)
          { // System.err.print ( "1 " ); 
          }
          rowbits[bcol] = 1;
        }
        else
        { if (debug) 
          { // System.err.print ( "0 " ); 
          }
          rowbits[bcol] = 0;
        }
      }

      // Make sure that the barcode rows have a width which is a 
      // multiple of 4 pixels
      for (int bcol=0; bcol<bcodeWidth; bcol+=4)  
      { int digit = rowbits[bcol]   * 8 +
                    rowbits[bcol+1] * 4 +
                    rowbits[bcol+2] * 2 +
                    rowbits[bcol+3] * 1 ;
        signedHash += hex[digit] ;
      }

      // if (debug) System.err.println (); 
    }
    // if (debug) System.err.println (); 

    if (graphics) { frame.repaint(); }

    if (raceErrors == 0) 
    { resultCode = 10; 
    }
    else if (raceErrors > 0) 
    { resultCode = 11; 
    }
    else 
    { resultCode = 12; 
    }

    int serialNoInt = 0;
    for (int ii=0; ii<8; ii++)
    { serialNoInt = serialNoInt * 16 + 
                        Character.digit(signedHash.charAt (256+ii), 16);
    }
    serialNoInt &= 0x7fffffff;

    System.out.print (resultCode + "," + serialNoInt + "," + 
                      signedHash.substring (0, 256) + "," +
                      numRaces + "," );
    for (int ii=0; ii<raceResult.length; ii++)
    { System.out.print (raceResult[ii] + ",");
    }
    for (int ii=0; ii<raceMessage.length; ii++)
    { System.out.print (raceMessage[ii] + ",");
    }
    System.out.print("," + args[0]);
    System.out.print("," + weights[0]);
    System.out.print("," + weights[1]);
    System.out.print("," + weights[2]);
    System.out.print("," + weights[3]);
    System.out.println("");

    
    if (graphics) { frame.repaint(); }
      
    /*
    while (true)
    {
      Thread.currentThread().sleep(1000);
      if (graphics) { frame.repaint(); }
    }
    */
    

  }  // end of main()



  /** Accumulate all pixels of a given colour into new set 
  *  @param myimage
  *  @param startx
  *  @param starty
  *  @param width
  *  @param height
  *  @param wras
  *  @param flood
  *  @param threshold
  *  @param lt
  *  @param seed1
  *  @param seed2
  *  @param newcolour
  *  @param tl
  *  @param bl
  *  @param tr
  *  @param br
  *  @param found boolean [][] found = new boolean [1+maxy-miny][1+maxx-minx];
  */
   private static int floodfill (int [][] myimage,
                                 int minx, int miny, int maxx, int maxy,
                                 WritableRaster wras,
                                 boolean flood,
                                 int threshold, 
                                 boolean lt, 
                                 Pair seed1, Pair seed2, 
                                 int [] newcolour, 
                                 Pair tl, Pair bl, Pair tr, Pair br,
                                 boolean [][] found)

  { HashSet <Pair> hash = new HashSet <Pair>();
    HashSet <Pair> newhash = new HashSet <Pair>();
    // System.err.println ("floodfill: " + 
                          // minx + " " + miny + " " + maxx + " " + maxy);
    int set=0;
    for (int rr=miny; rr<=maxy; rr++)
    { for (int ss=minx; ss<=maxx; ss++)
      { found[rr][ss] = false;
      }
    }
  
    // Set bounding box to mid-point of seed
    tl.update ((seed1.x + seed2.x)/2, (seed1.y + seed2.y)/2);
    bl.update ((seed1.x + seed2.x)/2, (seed1.y + seed2.y)/2);
    tr.update ((seed1.x + seed2.x)/2, (seed1.y + seed2.y)/2);
    br.update ((seed1.x + seed2.x)/2, (seed1.y + seed2.y)/2);

    // This should draw a single line between seed1 and seed2
    // Currently, it draws a rectangle between the points.
    for (int jj=seed1.y; jj<=seed2.y; jj++)
    { for (int ii=seed1.x; ii<=seed2.x; ii++)
      { 
          // wras.setPixel(ii, jj, new int[] {127,127,127,0});
        if ( (lt && (myimage[jj][ii] < threshold)) || 
          (!lt && (myimage[jj][ii] > threshold)) )
        { if (jj>=miny && jj<=maxy && ii>=minx && ii<=maxx && 
                                                   !found[jj-miny][ii-minx])
          { newhash.add (new Pair (ii, jj));
            found[jj-miny][ii-minx] = true;  
            set ++;
            // if (wras != null) 
            // { wras.setPixel(ii, jj, new int[] {255,0,255,0}); }
          }
        }
      }
    }

    int count = 1;

    while (count > 0)
    { Iterator <Pair> it = hash.iterator();

      count = 0;
      hash = newhash;
      // System.err.println (hash.size());

      newhash = new HashSet <Pair>();
      it = hash.iterator();
      while (it.hasNext())
      { // System.err.println (hash.size());
        Pair pp = it.next();
        int x = pp.x;
        int y = pp.y;
        int pix = 0;
        // int [] colour = new int[4] ;

        // Enlarge bounding box to contain point (x,y)
        if (x+y < tl.x + tl.y) tl.update (x, y);
        if (x-y < bl.x - bl.y) bl.update (x, y);
        if (x-y > tr.x - tr.y) tr.update (x, y);
        if (x+y > br.x + br.y) br.update (x, y);

        // Change from wras to myimage throughout
        // wras.getPixel(x, y, colour);
        int centrePix = myimage[y][x];

        // System.err.println ("Consider " + x + "  " + y + " " +
                          // centrePix);

        if ((wras != null) && (newcolour != null)) 
        { wras.setPixel(x, y, newcolour); 
        }

        // old test:  if ((!lt && pix > threshold) || (lt && pix < threshold))

        final int variance = 6;

        for (int yy=y-1; yy<=y+1; yy++)
        { for (int xx=x-1; xx<=x+1; xx++)
          { if (yy>=miny && yy<maxy && xx>=minx && xx<maxx && !found[yy-miny][xx-minx])
            { pix = myimage[yy][xx];
              if (Math.abs (centrePix - pix) < variance)
              { newhash.add (new Pair (xx,yy));
                found[yy-miny][xx-minx] = true;  
                set ++;
                count++;
              }
            }
          }
        }

      }
      if (!flood) count = 0;
    }
    // System.err.println ("floodfill: " + tl.x + ", " + tl.y);
    // System.err.println ("floodfill: " + bl.x + ", " + bl.y);
    // System.err.println ("floodfill: " + tr.x + ", " + tr.y);
    // System.err.println ("floodfill: " + br.x + ", " + br.y);

    return set;
  }


  private static class Template 
  { protected char value;
    protected int [][] template;
    protected int height, width;
    protected String filename;

    private Template (int [][] tmpl, String file)
    { template = tmpl;
      filename = file;
      height = tmpl.length;
      width = tmpl[0].length;
      value = '?';
    }

    private Template (int [][] tmpl, String file, char ch)
    { template = tmpl;
      filename = file;
      height = tmpl.length;
      width = tmpl[0].length;
      value = ch;
    }
  }


  private static class Pair 
  { protected int x, y;
    private Pair ()
    { x = 0; y = 0;
    }

    private Pair (int i, int j)
    { x = i; y = j;
    }

    private Pair (double f, double g)
    { x = (new Long (Math.round(f))).intValue(); 
      y = (new Long (Math.round(g))).intValue();
    }

    protected void update (int i, int j)
    { x = i; y = j;
    }
  }

  private static class MyMouseListener extends MouseInputAdapter
  { public void mousePressed (MouseEvent e) 
    { int x = e.getX();
      int y = e.getY();
      // System.err.println ("Mouse Pressed");
      System.exit(0);
    }
  }

  private static class MyKeyListener extends KeyAdapter
  { public void keyPressed (KeyEvent e) 
    { // System.err.println ("Key Pressed");
      char c = e.getKeyChar();
      if ((c == 'q') || (c == 'Q'))
      { // System.err.println ("Q Pressed");
        System.exit(0);
      }
    }
  }


}

