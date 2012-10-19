package org.scantegrity.common;

import java.awt.Color;
import java.awt.Graphics2D;

import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.awt.image.AffineTransformOp;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeMap;
import java.util.Vector;

import javax.imageio.ImageIO;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.BallotGeometryMap;
import org.scantegrity.common.Cluster;
import org.scantegrity.common.ImageToCoordinatesInches;
import org.scantegrity.common.Prow;

/**
 * Each ballot has two alignment marks. One close to the upper left corner and
 * the other close of the lower right corner.
 * 
 *  Each alignment mark is a non-white circle = two black circles. 
 *  
 *  For starter, we assume that the the width of the image is the width of the ballot.
 *  We can compute the dpi having this assumption. 
 *  
 *  How to correct for alignment:<BR>
 *  Stept1:<ul>
 *  	<li> Starting from where the alignmerks should be, search for
 *  black circles on a radius of half an inch.
 *  		If found, check that the black-cluster is a circle (
 *  		check if the surounding rectangle is a square and the disk
 *  		equation checks.) If it is not a circle, keep searching.
 *  	<li> do the same above for the lower right alignment mark
 *  </ul> 
 *  Stept2:<ul>
 *   	<li> compute the rotation angle, translation on x and Y and scalling factor
 *   based on the two alignment marks
 *   </ul>
 *   
 *   Once the alignment elements are computer:
 *   Step 3:<ul>
 *   <li> look where the serial number should be and OCR it.
 *   		The default assumption is that we have a top page.
 *   		if the OCR is not successufll, then we have a bottom page. Try looking there.
 *  		OCR success indicates a good ballot.
 *  </ul>
 *  Step 5:<ul>
 *  	<li> start loooking where marks should be. 
 *  	<li> a mark is considered filled in if the number of "black" pixels is 
 *  		more then a threshhold 
 *  </ul>   
 */
public class ScannedBallot implements ScannedBallotInterface {

	public static boolean debug=false;
	
	protected BallotGeometryMap bgm;

	Point2D.Double ul=null;
	Point2D.Double lr=null;	
		
	public static enum TypeOfVotes {NoVote,UnderVote,Vote,OverVote};
	
	protected int[] markPixels=null;
	TreeMap<Integer, TreeMap<Integer, TreeMap<Integer, Cluster>>> contests=null;
	TreeMap<Integer, TreeMap<Integer, TreeMap<Integer, TypeOfVotes>>>  markedContests=null;
	TreeMap<Integer,TypeOfVotes> racesCorrectness=null;
	
	private double perfectAngle;
	
	protected String serial=null;
	Prow.ChosenPage scannedPage=Prow.ChosenPage.NONE;
	boolean mailIn=false;
	
	protected Question[] qs=null;
	ElectionSpecification es=null;
	
	
	BufferedImage perfectImage=null;
	
	protected static float markThreasholdTop=0.2f;
	protected static float markThreasholdBottom=0.5f;
	
	double dpi=-1;
	
	int maxTotalNoAnswers=-1;

	protected double innerRadiusTop=-1;
	protected double outerRadiusTop=-1;

	protected double innerRadiusBottom=-1;
	protected double outerRadiusBottom=-1;

	protected int innerRadiusCurrent=-1;
	protected int outerRadiusCurrent=-1;
	protected int innerRadiusCurrentSquare=-1;
	protected int outerRadiusCurrentSquare=-1;
	
	protected boolean isFullVoted=false;
	
	/**
	 * Initialises the scanned ballot with the Geometry and the ELection Spec
	 * @param geom
	 * @param es
	 */
	public ScannedBallot(BallotGeometry geom, ElectionSpecification es) {
		this.es=es;
		this.qs=es.getOrderedQuestions();
		maxTotalNoAnswers=0;
		for (int q=0;q<qs.length;q++) {
			maxTotalNoAnswers+=qs[q].getMax();
		}
		
		bgm=new BallotGeometryMap(geom,es);
		//this.es=es;
		ul=geom.getUpperAlignment();
		lr=geom.getLowerAlignment();
		
		if (ul.x == lr.x)
			perfectAngle = Math.PI / 2;
		else
			perfectAngle = Math.atan((lr.getY() - ul.getY()) / (ul.getX()-lr.getX()));
		if (perfectAngle < 0)
			perfectAngle += Math.PI;
		
		innerRadiusTop=geom.getHoleDiameter()/2;
		outerRadiusTop=innerRadiusTop+geom.getDonutThicknessTop();

		outerRadiusBottom=geom.getHoleDiameter()/2;
		innerRadiusBottom=outerRadiusBottom-geom.getDonutThicknessBottom();
		
		contests=bgm.getMarkedContests();		
	}
	
	/** 
	 * @param img a perfectly aligned image
	 * @param dpi - the dpi of the image
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown 
	 */
	public void detectFromPerfectImage(BufferedImage img,double dpi) throws Exception {
		//detect the marks;
		markedContests=null;
		cloneContestTree();
		
		perfectImage=img;
		
		
		detectSerialFromPerfectImage(img, dpi);
		
		long start=System.currentTimeMillis();
		detectMarksFromPerfectImage(img, dpi);
	    //System.out.println("Detecting the marks took "+(System.currentTimeMillis()-start)+" milisseconds");
		
		if (debug) {
			try {
				Rectangle2D.Double rect=null;
				
				System.out.println("perfect"+bgm.getUpperAlignment());
				System.out.println("perfect+"+bgm.getLowerAlignment());
				
				Graphics2D g=img.createGraphics();
				g.setColor(Color.RED);
				
				//draw rectengles where the alignment marks should be
				Point2D.Double ul=bgm.getUpperAlignment();
				g.drawRect((int)(ul.getX()*dpi)-20, (int)(ul.getY()*dpi)-20, 40,40);
				
				Point2D.Double lr=bgm.getLowerAlignment();
				g.drawRect((int)(lr.getX()*dpi)-20, (int)(lr.getY()*dpi)-20, 40,40);
				
				rect=bgm.getSerialBottomRectangle();
				if (rect!=null)
					g.drawRect((int)(rect.getMinX()*dpi), (int)(rect.getMinY()*dpi), (int)(rect.getWidth()*dpi),(int)(rect.getHeight()*dpi));

				rect=bgm.getSerialTopRectangle();
				g.drawRect((int)(rect.getMinX()*dpi), (int)(rect.getMinY()*dpi), (int)(rect.getWidth()*dpi),(int)(rect.getHeight()*dpi));

				ImageIO.write(img,"png",new File("MarkedImage.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}				
		}
	}
	
	public void detectMarksFromPerfectImage(BufferedImage img,double dpi) {
		isFullVoted=true;
		for (Integer raceNo:contests.keySet()) {
			TreeMap<Integer, TreeMap<Integer, Cluster>> race=contests.get(raceNo);
			for (Integer rankNo:race.keySet()) {
				TreeMap<Integer, Cluster> rank=race.get(rankNo);
				for (Integer candidateNo:rank.keySet()) {
					if (isMarked(img,rank.get(candidateNo),dpi)) {
						if (debug )
							System.out.println("mark at "+raceNo+" "+rankNo+" "+candidateNo);
						markedContests.get(raceNo).get(rankNo).put(candidateNo, TypeOfVotes.Vote);						
					} else {
						isFullVoted=false;
					}
				}
			}
		}		
		//check for overvotes
		int noMarkedThisContest=0;
		int noMarkedThisRow=0;
		Set<Integer> allCandidatesSelectedInCurrentContest=null; 
		TypeOfVotes finalVote=null;

		racesCorrectness = new TreeMap<Integer, TypeOfVotes>();
		
		for (Integer raceNo:markedContests.keySet()) {
			racesCorrectness.put(raceNo, TypeOfVotes.Vote);
			
			noMarkedThisContest=0;
			finalVote=null;
			allCandidatesSelectedInCurrentContest=new HashSet<Integer>();
			for (Integer rankNo:markedContests.get(raceNo).keySet()) {
				noMarkedThisRow=0;
				for (Integer candidateNo:markedContests.get(raceNo).get(rankNo).keySet()) {
					if (markedContests.get(raceNo).get(rankNo).get(candidateNo).equals(TypeOfVotes.Vote)) {
						noMarkedThisRow++;
						allCandidatesSelectedInCurrentContest.add(candidateNo);
					}
				}
				//no two marks on the same row				
				if (qs[raceNo].getTypeOfAnswer().equals(Constants.RANK) && 
					noMarkedThisRow>1) {
						finalVote=TypeOfVotes.OverVote;
						racesCorrectness.put(raceNo, TypeOfVotes.OverVote);
					
						//System.out.println("Overvote, two candidates have the same rank");
					}
				noMarkedThisContest+=noMarkedThisRow;
			}
			
			//no two marks on the same column
			if (qs[raceNo].getTypeOfAnswer().equals(Constants.RANK) &&
				allCandidatesSelectedInCurrentContest.size()!=noMarkedThisContest) {
					finalVote=TypeOfVotes.OverVote;
					racesCorrectness.put(raceNo, TypeOfVotes.OverVote);
					
					//System.out.println("Overvote, one candidate has two ranks");
					
			}
			else
			if ((qs[raceNo].getTypeOfAnswer().compareTo(Constants.RANK)==0) &&
					noMarkedThisContest >0) {
				//let the contest be considered as normaly voted
				//to not for voters to rank all candidates (some may be write-ins)
			}
			else
			if (noMarkedThisContest>qs[raceNo].getMax()) {
				finalVote=TypeOfVotes.OverVote;
				racesCorrectness.put(raceNo, TypeOfVotes.OverVote);
			} 
			else
			if (noMarkedThisContest<qs[raceNo].getMax()&& noMarkedThisContest>0) {
				finalVote=TypeOfVotes.UnderVote;
				racesCorrectness.put(raceNo, TypeOfVotes.UnderVote);
			}
			else
			if (noMarkedThisContest==0) {
				finalVote=TypeOfVotes.UnderVote;
				racesCorrectness.put(raceNo, TypeOfVotes.NoVote);
			}

			if (finalVote!=null) {
				for (Integer rankNo:markedContests.get(raceNo).keySet()) {
					for (Integer candidateNo:markedContests.get(raceNo).get(rankNo).keySet()) {
						if (markedContests.get(raceNo).get(rankNo).get(candidateNo).equals(TypeOfVotes.Vote))						
							markedContests.get(raceNo).get(rankNo).put(candidateNo, finalVote);
					}
				}
			}
		}		
	}

	/**
	 * Tries to read the serial from whre it should on the top page, if unssucesful, tries
	 * to read the serial number from where it should be on the bottom page
	 * @param img
	 * @param dpi
	 * @throws Exception
	 */
	public void detectSerialFromPerfectImage(BufferedImage img,double dpi) throws Exception {

		//first detect the serial
		Rectangle2D.Double rect=bgm.getSerialTopRectangle();
		
		BufferedImage serialImage=img.getSubimage((int)(rect.getMinX()*dpi), (int)(rect.getMinY()*dpi), (int)(rect.getWidth()*dpi),(int)(rect.getHeight()*dpi));
		
		if (debug) {
			try {
				ImageIO.write(serialImage,"png",new File("SerialTop.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}				
		}		
		
 		scannedPage=Prow.ChosenPage.NONE;
 		serial="?";
		SerialNoRecognizer snr = new SerialNoRecognizer(); 		
		try {	
			serial = snr.recognize(serialImage, SerialNoRecognizer.NOT_WHITE,dpi);
			scannedPage=Prow.ChosenPage.TOP;
		} catch (Exception e) {
			e.printStackTrace();
			serial = "?";
		}		
		if (serial.length() != bgm.getNoDigitsInserial() || serial.compareTo("?")==0) {
			try {
				rect=bgm.getSerialBottomRectangle();
				serialImage = img.getSubimage((int)(rect.getMinX()*dpi), (int)(rect.getMinY()*dpi), (int)(rect.getWidth()*dpi),(int)(rect.getHeight()*dpi));
				
				if (debug) {
					try {
						ImageIO.write(serialImage,"png",new File("SerialBottom.png"));
					} catch (IOException e) {
						e.printStackTrace();
					}				
				}
				serial = snr.recognize(serialImage, SerialNoRecognizer.NOT_WHITE,dpi);
		 		scannedPage=Prow.ChosenPage.BOTTOM;
			} catch (Exception e) {
				e.printStackTrace();
				serial = "?";
				scannedPage=Prow.ChosenPage.NONE;
			}
			if (serial.length() != bgm.getNoDigitsInserial() || serial.compareTo("?")==0) {
				throw new Exception("The serial number ("+serial+")has |"+serial.length()+"| digits instead of |"+bgm.getNoDigitsInserial()+"|, as indicated by the ballotMap");				
			}
		}
		
		if (scannedPage.equals(Prow.ChosenPage.TOP)) {
			innerRadiusCurrent=(int)(innerRadiusTop*dpi);
			outerRadiusCurrent=(int)(outerRadiusTop*dpi);
		} else
		if (scannedPage.equals(Prow.ChosenPage.BOTTOM)) 
		{
			innerRadiusCurrent=(int)(innerRadiusBottom*dpi);
			outerRadiusCurrent=(int)(outerRadiusBottom*dpi);
		}
		
		innerRadiusCurrentSquare=innerRadiusCurrent*innerRadiusCurrent;
		outerRadiusCurrentSquare=outerRadiusCurrent*outerRadiusCurrent;		
	}
	
	/** 
	 * Clips the cluster from the image and checks if the clipped image
	 * has more "black" pixels then a threashold
	 * @param img
	 * @param c
	 * @param dpi
	 * @return 
	 */
/*	
	protected boolean isMarked(BufferedImage img, Cluster c, double dpi) {
		int fromx=(int)(c.getXmin()*dpi);		
		int fromy=(int)(c.getYmin()*dpi);
		int w=(int)(c.getXmax()*dpi)-fromx;
		int h=(int)(c.getYmax()*dpi)-fromy;
		
		return isMarked(img, fromx, fromy, w, h);
	}

	protected boolean isMarked(BufferedImage img, int fromx, int fromy,int w,int h) {
		if (debug)
			try {
				ImageIO.write(img.getSubimage(fromx, fromy, w, h),"png",new File(fromx+"_"+fromy+"Mark.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}
		
		if (markPixels==null || markPixels.length!=w*h)
			markPixels=new int[w*h];
		
		img.getRGB(fromx, fromy, w, h, markPixels,0, w);
		
		int xCenter=fromx+w/2;
		int yCenter=fromy+h/2;
		
		if (debug) {
			Graphics2D g=img.createGraphics();
			g.setColor(Color.RED);
			if (scannedPage.equals(Prow.ChosenPage.TOP)) {
				g.drawArc(fromx, fromy, w, h,0,360);
			}
			if (scannedPage.equals(Prow.ChosenPage.BOTTOM)) {
				System.out.println(markThreasholdBottom);
			}			
			g.drawRect(fromx, fromy, w, h);			
		}
		
		int count=0;
		for (int i=0;i<markPixels.length;i++) {
			//count the number of offwhite points
			Color color=new Color(markPixels[i]);
			if ( ((Math.abs(color.getRed() - 255) + Math.abs(color.getGreen()-255) + Math.abs(color.getBlue()-255))) > 100 ){
				count++;
			}
		}
		float greyArea=((float)count/(w*h));
		
		if (debug) {
			System.out.print("fromx="+fromx+" fromy="+fromy+" grayArea="+greyArea+" threashold=");
			if (scannedPage.equals(Prow.ChosenPage.TOP)) {
				System.out.println(markThreasholdTop);
			}
			if (scannedPage.equals(Prow.ChosenPage.BOTTOM)) {
				System.out.println(markThreasholdBottom);
			}			
		}
		
		if (scannedPage.equals(Prow.ChosenPage.TOP) && greyArea > markThreasholdTop) {
			return true;
		}

		if (scannedPage.equals(Prow.ChosenPage.BOTTOM) && greyArea > markThreasholdBottom) {
			return true;
		}
		
		return false;
	}
*/
	
	protected boolean isMarked(BufferedImage img, Cluster c, double dpi) {
		int fromx=(int)(c.getXmin()*dpi);		
		int fromy=(int)(c.getYmin()*dpi);
		int w=(int)(c.getXmax()*dpi)-fromx;
		int h=(int)(c.getYmax()*dpi)-fromy;
		
		int xCenter=fromx+w/2;
		int yCenter=fromy+h/2;
				
		return isMarked(img, xCenter,yCenter);
	}

	protected boolean isMarked(BufferedImage img, int xCenter, int yCenter) {
		int fromx=xCenter-outerRadiusCurrent;
		int fromy=yCenter-outerRadiusCurrent;
		int w=2*outerRadiusCurrent;
		int h=2*outerRadiusCurrent;
		
		if (debug) {
			Graphics2D g=img.createGraphics();
			g.setColor(Color.RED);
			//draw the outer circle
			g.drawArc(fromx, fromy, w, h,0,360);
			//draw the inner circle
			g.drawArc(fromx+(outerRadiusCurrent-innerRadiusCurrent), fromy+(outerRadiusCurrent-innerRadiusCurrent), 2*innerRadiusCurrent, 2*innerRadiusCurrent,0,360);
			
			try {
				ImageIO.write(img.getSubimage(fromx, fromy, w, h),"png",new File(fromx+"_"+fromy+"Mark.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		if (markPixels==null || markPixels.length!=w*h)
			markPixels=new int[w*h];
		
		img.getRGB(fromx, fromy, w, h, markPixels,0, w);
						
		int count=0;
		int i,j;
		for (int ii=0;ii<markPixels.length;ii++) {
			i=ii/h-outerRadiusCurrent;
			j=ii%h-outerRadiusCurrent;			
			//count the number of offwhite points
			int rSquere=i*i+j*j;
			//the point has to be in the outer circle, but not in the inner one
			if (rSquere<=outerRadiusCurrentSquare && rSquere>=innerRadiusCurrentSquare) {				
				Color color=new Color(markPixels[ii]);
				if ( ((Math.abs(color.getRed() - 255) + Math.abs(color.getGreen()-255) + Math.abs(color.getBlue()-255))) > 100 ){
					count++;
				}
			}
		}
		double greyArea=count / (Math.PI*(outerRadiusCurrentSquare-innerRadiusCurrentSquare));
		
		if (debug) {
			System.out.print("fromx="+fromx+" fromy="+fromy+" grayArea="+greyArea+" ");
			System.out.println(scannedPage+" "+markThreasholdTop+" "+markThreasholdBottom);
		}
		
		if (scannedPage.equals(Prow.ChosenPage.TOP)) {
			if (greyArea > markThreasholdTop) 
				return true;
			 return false;
		}
		if (scannedPage.equals(Prow.ChosenPage.BOTTOM)) {
			if (greyArea > markThreasholdBottom)
				return true;
			return false;
		}		

		if (greyArea > markThreasholdTop) 
			return true;
		
		return false;
	}
	
	

	public void detect(BufferedImage img) throws Exception {
		dpi=img.getWidth()/bgm.getWidth();
//System.out.println("dpi="+dpi);		
		//check if the alignment marks are where they should be.
		
		int b=70;
		Cluster black=new Cluster(new Color(b,b,b),new Color(b,b,b),0.05);
		
		long start=System.currentTimeMillis();
		ImageToCoordinatesInches itc=new ImageToCoordinatesInches(img,dpi, null);
		//System.out.println("Making ImageToCoordinatesInches took "+(System.currentTimeMillis()-start)+" milisseconds");
		
		Cluster ulc=null;		
		
		start=System.currentTimeMillis();
		long timeToWait=1000;//1seconds
		boolean timeout=false;
		do {
			if (System.currentTimeMillis()-start>timeToWait) {
				timeout=true;
				break;
			}			
			ulc=itc.detectCircular(ul.getX(), ul.getY(), 0.5, black);
//System.out.println(ulc);			
		} while (ulc !=null && !isCircle(img, ulc) && !timeout);
		
		if (timeout)
			throw new Exception("Cound not detect upper left alignment mark in "+(timeToWait/1000)+" seconds. Aborting");
		if (ulc==null)
			throw new Exception("Cannot detect Upper left alignment mark. Aborting");

//System.out.println("Detecting one alignment mark took "+(System.currentTimeMillis()-start)+" milisseconds");
		
		Cluster lrc=null;
		start=System.currentTimeMillis();
		timeout=false;
		do {
//System.out.println(lrc+" "+lr.getX()+" "+lr.getY());			
			if (System.currentTimeMillis()-start>timeToWait) {
				timeout=true;
				break;
			}
			lrc=itc.detectCircular(lr.getX(), lr.getY(), 0.5, black);			
		} while(ulc !=null && !isCircle(img, lrc) && !timeout);

		if (timeout)
			throw new Exception("Cound not detect lower right alignment mark in "+(timeToWait/1000)+" seconds. Aborting");
		
		if (lrc==null)
			throw new Exception("Cannot detect lower right alignment mark. Aborting");
		
//System.out.println("Detecting one alignment mark took "+(System.currentTimeMillis()-start)+" milisseconds");		
		
		//make the image perfectly aligned
start=System.currentTimeMillis();
		BufferedImage corectedImage=computeTransformation(img, ulc.getCenterOfMass(),lrc.getCenterOfMass(), dpi);
//System.out.println("Making the image perfect took "+(System.currentTimeMillis()-start)+" milisseconds");						
			if (debug) {
				
/*				
				itc=new ImageToCoordinatesInches(corectedImage,dpi, null);
				ulc=null;
				do { 
					ulc=itc.detectCircular(ul.getX(), ul.getY(), 0.2, black);
				} while (ulc !=null && !isCircle(img, ulc));
				lrc=null;
				do {
					lrc=itc.detectCircular(lr.getX(), lr.getY(), 0.2, black);
				} while(ulc !=null && !isCircle(img, lrc));
*/				
				
				Graphics2D g=corectedImage.createGraphics();
				g.setColor(Color.GREEN);
				
				//draw rectangles where the alignment marks are
				g.drawRect((int)(ulc.getCenterOfMass().getX()*dpi)-20,(int)(ulc.getCenterOfMass().getY()*dpi)-20,40,40);
				g.drawRect((int)(lrc.getCenterOfMass().getX()*dpi)-20,(int)(lrc.getCenterOfMass().getY()*dpi)-20,40,40);
				
				g.setColor(Color.BLUE);
				//draw rectengles where the alignment marks should be
				Point2D.Double ul=bgm.getUpperAlignment();
				g.drawRect((int)(ul.getX()*dpi)-20, (int)(ul.getY()*dpi)-20, 40,40);
				
				Point2D.Double lr=bgm.getLowerAlignment();
				g.drawRect((int)(lr.getX()*dpi)-20, (int)(lr.getY()*dpi)-20, 40,40);
				
				System.out.println("perfect "+bgm.getUpperAlignment());
				System.out.println("detected "+ulc.getCenterOfMass());
				System.out.println("perfect "+bgm.getLowerAlignment());
				System.out.println("detected "+lrc.getCenterOfMass());
			}
			
			detectFromPerfectImage(corectedImage,dpi);
	}

	/**	 
	 * @param sul - scanned upper left
	 * @param slr - scanned lower right
	 */
	private BufferedImage computeTransformation(BufferedImage img, Point2D.Double sul, Point2D.Double slr, double dpi) throws Exception {
		//local upper left
		Point2D.Double lul=new Point2D.Double(ul.getX(),ul.getY());
		//local lower right
		Point2D.Double llr=new Point2D.Double(lr.getX(),lr.getY());
				
		//scalling
		double scale = lul.distance(llr) / sul.distance(slr);
		
		//if (Math.abs(scale-1)<0.02)	scale=1;
		
		if (debug) {System.out.println("Scale="+scale);}
		AffineTransform scaleTransform = AffineTransform.getScaleInstance(scale,scale); 
		scaleTransform.transform(sul,sul);		
		scaleTransform.transform(slr,slr);
		
		//rotation
		double scannedAngle = 0;
		if (lul.getX() == llr.getX())
			scannedAngle = Math.PI / 2;
		else
			scannedAngle = Math.atan(((slr.getY() - sul.getY())) / (sul.getX()-slr.getX()));
		if (scannedAngle < 0)
			scannedAngle += Math.PI;
		double rotationAngle = scannedAngle-perfectAngle;
		
		//if (Math.abs(rotationAngle / Math.PI * 180)<1) rotationAngle=0;
		
		if (debug) {System.out.println("perfect angle="+(perfectAngle / Math.PI * 180)+" scannedAngle="+(scannedAngle / Math.PI * 180)+" rotation="+(rotationAngle / Math.PI * 180));}
		Point2D.Double pivot=slr;
		AffineTransform rotationTransform = AffineTransform.getRotateInstance(rotationAngle,pivot.getX(),pivot.getY());
		rotationTransform.transform(sul,sul);
				
		//translation
		double tx = llr.getX()-slr.getX();
		double ty = llr.getY()-slr.getY();
		
		//if (Math.abs(tx)<0.04) tx=0;
		//if (Math.abs(ty)<0.04) ty=0;
		
		if (debug) {System.out.println("tx="+tx+" ty="+ty);}
		AffineTransform translateTransform = AffineTransform.getTranslateInstance(tx,ty); 
		translateTransform.transform(sul,sul);
		translateTransform.transform(slr,slr);		
				
		
		//make the image perfect
		img=transformImageAllAffineTransformationsAtOnce(img, scale, pivot, rotationAngle, tx, ty);
		
		//clip
//		ret=ret.getSubimage(0,0,(int)(bgm.getWidth()*150),(int)(bgm.getHeight()*150));
		
		double alignbmentErrorAllowed = 0.18;//inches
		if (Math.abs(llr.getX()-slr.getX()) > alignbmentErrorAllowed
				|| Math.abs(llr.getY()-slr.getY()) > alignbmentErrorAllowed)
			throw new Exception("Lower Right alignment failed. Should be at ("+llr.getX()+","+llr.getY()+") but is at ("+slr.getX()+","+slr.getY()+")");
		if (Math.abs(lul.getX()-sul.getX()) > alignbmentErrorAllowed
				|| Math.abs(lul.getY()-sul.getY()) > alignbmentErrorAllowed )
			throw new Exception("Upper Right alignment failed. Should be at ("+lul.getX()+","+lul.getY()+") but is at ("+sul.getX()+","+sul.getY()+")");		

		return img;
	}
	
	BufferedImage transformImage(BufferedImage img, double scale, Point2D pivot, double rotationAngle, double tx, double ty) {
		BufferedImage transformed=new BufferedImage(img.getWidth(),img.getHeight(),img.getType());
		BufferedImage temp=null;
		
		AffineTransformOp transform=null;
		transform=new AffineTransformOp(AffineTransform.getScaleInstance(scale,scale),AffineTransformOp.TYPE_BILINEAR);
		//System.out.println(transform.getBounds2D(ret));
		//scale
		transform.filter(img,transformed);
		temp=transformed;
		transformed=img;
		img=temp;
		
		if (debug) {
			try {
				ImageIO.write(transformed,"png",new File("Scaled.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}				
		}
		//rotate
		pivot=new Point2D.Double(pivot.getX()*dpi,pivot.getY()*dpi);
		transform=new AffineTransformOp(AffineTransform.getRotateInstance(rotationAngle,pivot.getX(),pivot.getY()),AffineTransformOp.TYPE_BILINEAR);
		//System.out.println(transform.getBounds2D(ret));
		transform.filter(img,transformed);
		temp=transformed;
		transformed=img;
		img=temp;
		
		if (debug) {
			try {
				ImageIO.write(img,"png",new File("Rotated.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}				
		}
		//translate
		transform=new AffineTransformOp(AffineTransform.getTranslateInstance(tx*dpi,ty*dpi),AffineTransformOp.TYPE_BILINEAR);
		//System.out.println(transform.getBounds2D(ret));
		transform.filter(img,transformed);
		temp=transformed;
		transformed=img;
		img=temp;

		if (debug) {
			try {
				ImageIO.write(img,"png",new File("Translated.png"));
			} catch (IOException e) {
				e.printStackTrace();
			}				
		}	
		return img;
	}

	BufferedImage transformImageAllAffineTransformationsAtOnce(BufferedImage img, double scale, Point2D pivot, double rotationAngle, double tx, double ty) {
		AffineTransform affineTransform = AffineTransform.getScaleInstance(scale,scale);
		affineTransform.concatenate(AffineTransform.getRotateInstance(rotationAngle,pivot.getX(),pivot.getY()));
		affineTransform.concatenate(AffineTransform.getTranslateInstance(tx*dpi,ty*dpi));

		AffineTransformOp transform=new AffineTransformOp(affineTransform,AffineTransformOp.TYPE_BILINEAR);
		//System.out.println(transform.getBounds2D(ret));

		BufferedImage transformed=new BufferedImage(img.getWidth(),img.getHeight(),img.getType());
		transform.filter(img,transformed);
		return transformed;
	}

	
	private boolean isCircle(BufferedImage img, Cluster c) {
		if (c==null)
			return false;
		int fromx=(int)(c.getXmin()*dpi);
		int fromy=(int)(c.getYmin()*dpi);
		int w=(int)(c.getXmax()*dpi)-fromx;
		int h=(int)(c.getYmax()*dpi)-fromy;
		
		if (Math.abs(w-h)/dpi>0.05)
			return false;
		
		int r=w<h?w:h;
		r/=2;
		
//		System.out.println("r "+r+" dpi "+dpi+" r/dpi "+r/dpi+ " "+w+ " "+h);
		
		if (Math.abs(r/dpi-0.14)>0.05) return false;
		
		int r2=r*r;
		int xc=fromx+w/2;
		int yc=fromy+h/2;
		
		int count=0;
		for (int y=fromy;y<=fromy+h;y++) {
			for (int x=fromx;x<=fromx+w;x++) {
				if ((x-xc)*(x-xc)+(y-yc)*(y-yc)<=r2) {
					Color color=new Color(img.getRGB(x,y));
					if (color.getRed()+color.getGreen()+color.getBlue() < 100 ){
						count++;
					}					
				}
			}
		}
		
		if (c.getNumberofPoints()*dpi-count>0.9)
			return true;
		return false;
	}
	
	public byte[] toXMLString() {
		StringBuffer s=new StringBuffer("<xml><ballot id=\""+serial+"\" type=\"");

		if (getSelectedPage().equals(Prow.ChosenPage.NONE))
			s.append("none");
		else					
			if (getSelectedPage().equals(Prow.ChosenPage.TOP) ^ mailIn)
				s.append("top");
			else
				s.append("bottom");

		s.append("\">\n");
		
		for (Integer contest:markedContests.keySet()) {
			s.append("\t<q"+contest+">\n");
			for (Integer row:markedContests.get(contest).keySet()) {
				for (Integer candidate:markedContests.get(contest).get(row).keySet()) {
					if (markedContests.get(contest).get(row).get(candidate).equals(TypeOfVotes.Vote)
							|| markedContests.get(contest).get(row).get(candidate).equals(TypeOfVotes.UnderVote)
							)
						s.append("\t\t<dot>"+candidate+"</dot>\n");
				}
			}
			s.append("\t</q"+contest+">\n");			
		}
		s.append("</ballot></xml>");
		return s.toString().getBytes();		
	}
	
	public String getCompactRepresentation() {
		StringBuffer s=new StringBuffer("");
		if (getSelectedPage().equals(Prow.ChosenPage.NONE))
			s.append("N");
		else			
			if (getSelectedPage().equals(Prow.ChosenPage.TOP) ^ mailIn)
				s.append("T");
			else
				s.append("B");

		s.append(serial+" ");

		int noCandidatesSelected=0;
		for (Integer contest:markedContests.keySet()) {
			noCandidatesSelected=0;
			for (Integer row:markedContests.get(contest).keySet()) {
				for (Integer candidate:markedContests.get(contest).get(row).keySet()) {
					if (markedContests.get(contest).get(row).get(candidate).equals(TypeOfVotes.Vote)
							|| markedContests.get(contest).get(row).get(candidate).equals(TypeOfVotes.UnderVote)
							) {
						s.append(candidate+" ");
						noCandidatesSelected++;
					}
				}
			}
			for (int j=noCandidatesSelected;j<qs[contest].getMax();j++) {
				s.append("-1 ");
			}
		}
		return s.toString();		
	}

	public Prow toProw() {
		Prow prow=new Prow();
		 
		prow.setId(Integer.parseInt(serial));
		
		if (getSelectedPage().equals(Prow.ChosenPage.NONE))
			prow.setChosenPage(Prow.ChosenPage.NONE);
		else			
			if (getSelectedPage().equals(Prow.ChosenPage.TOP) ^ mailIn)
				prow.setChosenPage(Prow.ChosenPage.TOP);
			else			
				prow.setChosenPage(Prow.ChosenPage.BOTTOM);

		byte[] vote=new byte[maxTotalNoAnswers];
		for (int i=0;i<vote.length;i++)
			vote[i]=-1;
		
		int votepos=0;
		int noCandidatesSelected=0;
		boolean isOneCandidateSelected=false;
		for (Integer contest:markedContests.keySet()) {
			noCandidatesSelected=0;
			for (Integer row:markedContests.get(contest).keySet()) {
				isOneCandidateSelected=false;
				for (Integer candidate:markedContests.get(contest).get(row).keySet()) {
					if (markedContests.get(contest).get(row).get(candidate).equals(TypeOfVotes.Vote)
							|| markedContests.get(contest).get(row).get(candidate).equals(TypeOfVotes.UnderVote)
							) {
						vote[votepos++]=(byte)(candidate+0);
						isOneCandidateSelected=true;
						noCandidatesSelected++;
					}
				}
				if (!isOneCandidateSelected) {
					vote[votepos++]=-1;
					noCandidatesSelected++;
				}
			}
			for (int j=noCandidatesSelected;j<qs[contest].getMax();j++) {
				vote[votepos++]=-1;
			}
		}
		prow.setVote(vote);
		return prow;		
	}	
	
	private void cloneContestTree() {
		markedContests= new TreeMap<Integer, TreeMap<Integer,TreeMap<Integer,TypeOfVotes>>>();;
		
		for (Integer contest:contests.keySet()) {
			TreeMap<Integer,TreeMap<Integer,TypeOfVotes>> rankTreeMap=new TreeMap<Integer, TreeMap<Integer,TypeOfVotes>>();
			for (Integer row:contests.get(contest).keySet()) {
				TreeMap<Integer,TypeOfVotes> candidateTreeMap=new TreeMap<Integer, TypeOfVotes>();
				for (Integer candidate:contests.get(contest).get(row).keySet()) {
					candidateTreeMap.put(candidate, TypeOfVotes.NoVote);
				}
				rankTreeMap.put(row, candidateTreeMap);
			}
			markedContests.put(contest,rankTreeMap);
		}		
	}

	public String getSerial() {
		return serial;
	}	

	public Vector<Cluster> getFullVotes() {
		return getVotes(TypeOfVotes.Vote);
	}
	
	public Vector<Cluster> getOverVotes() {
		return getVotes(TypeOfVotes.OverVote);
	}

	public Vector<Cluster> getUnderVotes() {
		return getVotes(TypeOfVotes.UnderVote);
	}
	
	public Vector<Cluster> getVotes(TypeOfVotes vote) {
		Vector<Cluster> ret=new Vector<Cluster>();
		for (Integer contest:markedContests.keySet()) {
			for (Integer row:markedContests.get(contest).keySet()) {
				for (Integer candidate:markedContests.get(contest).get(row).keySet()) {
					if (markedContests.get(contest).get(row).get(candidate).equals(vote)) {
						Cluster c=new Cluster(contests.get(contest).get(row).get(candidate));
						ret.add(c);
					}
				}
			}
		}		
		return ret;
	}	
	
	public Prow.ChosenPage getSelectedPage() {
		return scannedPage;
	}

	public BufferedImage getPerfectImage() {
		return perfectImage;
	}
	
	public double getDpi() {
		return dpi;
	}
	
	public BallotGeometryMap getBallotGeometryMap() {
		return bgm;
	}
	
	public TreeMap<Integer, TreeMap<Integer, TreeMap<Integer, TypeOfVotes>>> getAllContests() {
		return markedContests;
	}

	public boolean isMailIn() {
		return mailIn;
	}

	public void setMailIn(boolean mailIn) {
		this.mailIn = mailIn;
	}
	
	public TreeMap<Integer, TypeOfVotes> getRacesCorrectness() {
		return racesCorrectness;
	}

	public int containsWritein() throws Exception {
		throw new Exception("PunchScan ballots do not know if they contain writeins");
	}
	
	public boolean isFullyMarked() {
		return isFullVoted;
	}
	
	public ElectionSpecification getElectionSpec() {
		return es;
	}	
	
	public static void main(String[] args) throws Exception {
		String dir="Elections/CPSR/7And1/";
		BallotGeometry geom=new BallotGeometry(dir+"geometry.xml");
		ElectionSpecification es= new ElectionSpecification(dir+"ElectionSpec.xml");
		ScannedBallot sb=new ScannedBallot(geom,es);
		BufferedImage img=null;
		
		img=ImageIO.read(new File(dir+"images/MR1188307265974.bmp"));
		sb.detect(img);
		System.out.println(sb.toProw());
		//System.out.println(sb.getCompactRepresentation());
		
		//img=ImageIO.read(new File(dir+"scannes/8.bmp"));
		//sb.detect(img);
		//System.out.println(sb.toProw());

		//img=ImageIO.read(new File(dir+"scannes/9.bmp"));
		//sb.detect(img);
		//System.out.println(sb.toProw());

	}
}