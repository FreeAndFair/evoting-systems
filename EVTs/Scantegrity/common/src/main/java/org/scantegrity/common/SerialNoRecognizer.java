package org.scantegrity.common;

import java.awt.Color;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Iterator;
import java.util.TreeMap;
import java.util.Vector;

import javax.imageio.ImageIO;

import org.scantegrity.common.Cluster;
import org.scantegrity.common.ImageToCoordinatesInches;
/**
 * Given an image with a serial number on it (horizontally streigth), it tries to
 * detect the serial number. 
 * 
 * Only the offwhite method is used...For each off whitecluster, the digit with
 * the lower hamming distance from the definition is returned. 
 *  
 * @author stefan
 *
 */
public class SerialNoRecognizer {

	public static int OCR_ENGINE_GOCR = 0;
	public static int NOT_WHITE = 2;
	
	
	DigitDeffinition digitDefinition = null;
	double redFraction = 1.4;	
	
	public SerialNoRecognizer() {
		digitDefinition = new DigitDeffinition();
	}
	
	public String recognize(BufferedImage bufferedImage,int typeOfRecognitionUsed, double dpi) throws Exception
	{
		if (typeOfRecognitionUsed == OCR_ENGINE_GOCR)
			return recognizeGOCR(bufferedImage);
		if (typeOfRecognitionUsed == NOT_WHITE)
			return recognizeNotWhite(bufferedImage,dpi);
		throw new Exception ("undefined type of nethod to be used for recognition");
	}
	
	/**
	 * @deprecated No recomented, GOCR seems to give poor results.
	 * 
	 * @param bufferedImage
	 * @return the serial number detected with GOCR
	 * @throws Exception
	 */	
	public static String recognizeGOCR(BufferedImage bufferedImage) throws Exception
	{
		String serialFile = "serial.txt";
		String imageType="png";
		String imageFileName = "serial."+imageType;
		int numberOfDigitsInSerial = 5;
		
		String[] commands = {"org.scantegrity/scanner/IView/i_view32.exe serial.bmp /gray  /convert=serial.pbm","org.scantegrity/scanner/GOCR/gocr.exe -i serial.pbm -o serial.txt"};

		File imageFile = new File(imageFileName);
		ImageIO.write(bufferedImage,"png",imageFile);
		
		for (int i=0;i<commands.length;i++) {
			Process process = Runtime.getRuntime().exec(commands[i]);
			process.waitFor();
			if (process.exitValue() !=0 )
				throw new Exception("executing "+commands[i]+" failed with exit code "+process.exitValue());
			closeProcess(process);
		}		
		FileInputStream fis = new FileInputStream(serialFile);
		byte[] serial = new byte[fis.available()];
		fis.read(serial);
		String ret =new String(serial);
		fis.close();
		//imageFile.delete();
		if (ret.length()!=numberOfDigitsInSerial) {
			throw new Exception("The serial number |"+ret+"| does not have "+ numberOfDigitsInSerial+" digits");
		}
		return ret;		
	}
	
	private static void closeProcess(Process p_process) {
		try {
			if(p_process != null) {
				p_process.getErrorStream().close();
				p_process.getInputStream().close(); 
				p_process.getOutputStream().close(); 
			}
		} catch (Exception e) {
			//do nothing
		}		
	}

	/**
	 * Given an image with a serial number on it (horizontally streigth), it tries to
	 * detect the serial number. 
	 * 
	 * Only the offwhite method is used...For each off whitecluster, the digit with
	 * the lower hamming distance from the definition is returned. 
	 * 
	 * The algorithm is the folowing:
	 * <br>
	 * <ol>
	 * <li> detect an off white cluster
	 * Once detected the cluster, clip it and apply the following adaptive algorithm<BR>
	 * transform the cluster into a matrix of size the deffinition of the digit<BR>
	 * Find the color of the first pixel. 1=black, 0=white<BR>
	 *  current = 1, new higher -> if the difference is &gt threshold, make the new 0, otherwise new=1<BR>
	 *  current = 1, new lower ->  make the new 1<BR>
	 *  current = 0, new higher -> make new =0<BR>
	 *  current = 0, new lower -> if the difference &gt threshold, make new=1, otherwise new=0<BR> 
	 * <li> once digitized, find the definition digit with the smallest hamming distance 
	 * </ol>
	 * 
	 * @param bi an image with a serial number on it (horizontally streigth)
	 * @return the serial number detected in the image
	 * @throws Exception
	 */	
	public String recognizeNotWhite(BufferedImage bi, double dpi) throws Exception
	{
		String retVal="";
		//detect the clusters that are close to black. 
		double blackDiscontinuity = 0.1*dpi;//inches
		int b=80;
		Color black = new Color(b,b,b);
		Color blackVariation = new Color(b,b,b);
		Vector<Cluster> blackClusters =new Vector<Cluster>();
		blackClusters.add(new Cluster(black,blackVariation,blackDiscontinuity));
		ImageToCoordinatesInches itc = new ImageToCoordinatesInches(bi,1,blackClusters);
		Cluster digit = null;
		TreeMap<Integer, Character> tm = new TreeMap<Integer, Character>();
		while ((digit=itc.getNextCluster()) !=null) {
if (ScannedBallot.debug) System.out.println("OCR found "+digit);
			if (digit.getXmax()-digit.getXmin() > 1 && digit.getYmax()-digit.getYmin() > 1) 
			{

				
				int x= (int)digit.getXmin();
				int y= (int)digit.getYmin();
				int w= (int)(digit.getXmax()-digit.getXmin()+1);
				int h= (int)(digit.getYmax()-digit.getYmin()+1);
				BufferedImage digitImage = bi.getSubimage(x,y,w,h);

				if (ScannedBallot.debug)				
					try {
						String fName = "serial_"+x+"_"+y+".png";			
						ImageIO.write(digitImage,"png",new File(fName));
					} catch (IOException e) {
						e.printStackTrace();
					}
				
				Character c=null;
				try {
					c=new Character(detectDigitHamming(digitImage));
					tm.put(new Integer(x),c);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
		for (Iterator i = tm.values().iterator();i.hasNext();) {
			retVal+=((Character)i.next()).charValue();
		}

		return retVal;
	}
	
	
	/**
	 * 1. transform the image into a matrix of size the deffinition of the digit 
	 * @param bi
	 * @param redCluster
	 * @return
	 */
	private char detectDigitHamming(BufferedImage bi) throws Exception {
		int deffinitionDigitWidth = digitDefinition.getDigitWidth();
		int deffinitionDigitHeigth = digitDefinition.getDigitHeight();

		/*
		while (bi.getWidth()<deffinitionDigitWidth*1.5) {
			bi=new AffineTransformOp(AffineTransform.getScaleInstance(2,2),AffineTransformOp.TYPE_BILINEAR).filter(bi, null);
			if (ScannedBallot.debug)				
				try {
					String fName = "serial_w"+bi.getWidth()+"_"+bi.getHeight()+".png";			
					ImageIO.write(bi,"png",new File(fName));
				} catch (IOException e) {
					e.printStackTrace();
				}
		}
		while (bi.getHeight()<deffinitionDigitHeigth*1.5) {
			bi=new AffineTransformOp(AffineTransform.getScaleInstance(2,2),AffineTransformOp.TYPE_BILINEAR).filter(bi, null);
		}
		 */
		
		double scannedPixelWidth = (double)bi.getWidth() / deffinitionDigitWidth;
		double scannedPixelHeigth = (double)bi.getHeight() / deffinitionDigitHeigth;
		
		byte[][] scannedDigit = new byte[deffinitionDigitHeigth][deffinitionDigitWidth];
/*
		for (int j=0;j<deffinitionDigitHeigth;j++) {
			for (int i=0;i<deffinitionDigitWidth;i++) {
				//see if the current scanned pixel is black or white
				BufferedImage currentPixel = bi.getSubimage((int)Math.round(i*scannedPixelWidth),(int)Math.round((j*scannedPixelHeigth)),(int)scannedPixelWidth,(int)scannedPixelHeigth);
				int averageColor = averageImageColor(currentPixel);				
				if (averageColor < 175 )
					scannedDigit[j][i] = 1;
				else
					scannedDigit[j][i] = 0;
System.out.print(averageColor+" ");				
			}
System.out.println();			
		}
		*/
		
		/* Adapttive algorithm
		 * Find the color of the first pixel. 1=black, 0=white
		 *  current = 1, new higher -> if the difference is > threshold, make the new 0, otherwise new=1
		 *  current = 1, new lower ->  make the new 1
		 *  current = 0, new higher -> make new =0
		 *  current = 0, new lower -> if the difference > threshold, make new=1, otherwise new=0
		 */
		int threshold = 40;
		for (int j=0;j<deffinitionDigitHeigth;j++) {
			BufferedImage currentPixel = bi.getSubimage((int)Math.round(0*scannedPixelWidth),(int)Math.round((j*scannedPixelHeigth)),(int)Math.max(1,scannedPixelWidth),(int)Math.max(1,scannedPixelHeigth));			
			int currentAverage = averageImageColor(currentPixel);				
			if (currentAverage < 175 )
				scannedDigit[j][0] = 1;
			else
				scannedDigit[j][0] = 0;
			int newAverage = 0;
//System.out.print(currentAverage+" ");
if (ScannedBallot.debug) System.out.print(scannedDigit[j][0]+" ");			
			for (int i=1;i<deffinitionDigitWidth;i++) {
				//see if the current scanned pixel is black or white
				currentPixel = bi.getSubimage((int)Math.min(bi.getWidth()-1, Math.round(i*scannedPixelWidth)),(int)Math.min(bi.getHeight()-1,Math.round((j*scannedPixelHeigth))),(int)Math.max(1,scannedPixelWidth),(int)Math.max(1,scannedPixelHeigth));				
				newAverage = averageImageColor(currentPixel);				
				if (scannedDigit[j][i-1]==1)
					if (newAverage > currentAverage)
						if (newAverage-currentAverage > threshold)
							scannedDigit[j][i]=0;
						else
							scannedDigit[j][i]=1;
					else 
						scannedDigit[j][i]=1;
				if (scannedDigit[j][i-1]==0)
					if (newAverage > currentAverage)
						scannedDigit[j][i]=0;
					else
						if (currentAverage-newAverage > threshold)
							scannedDigit[j][i]=1;
						else
							scannedDigit[j][i]=0;
				currentAverage = newAverage;
//System.out.print(currentAverage+" ");
if (ScannedBallot.debug) System.out.print(scannedDigit[j][i]+" ");				
			}
if (ScannedBallot.debug) System.out.println();			
		}
		
		char ret=digitDefinition.minHammingDistance(scannedDigit);
		if (ScannedBallot.debug)
			System.out.println("Detected "+ret+" hamming distance "+digitDefinition.getMinDistance()+ " "+(double)digitDefinition.getMinDistance()/digitDefinition.getMaxDistance()*100+"%");
		return ret;
	}

	private int averageImageColor(BufferedImage img) {
		int sum = 0;
		for (int j=0;j<img.getHeight();j++)
			for (int i=0;i<img.getWidth();i++) {
				Color color = new Color(img.getRGB(i,j));
				sum=sum+((color.getRed()+color.getGreen()+color.getBlue())/3);
			}
		return (sum/(img.getHeight()*img.getWidth()));
	}
	
	/**
	 * Debug method
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception {
		/*
		String[] formats = ImageIO.getWriterFormatNames();
		for (int i=0;i<formats.length;i++)
			System.out.println(formats[i]);
		*/

		BufferedImage bi = ImageIO.read(new File(args[0]));
		SerialNoRecognizer snr = new SerialNoRecognizer();
		System.out.println(snr.recognize(bi, SerialNoRecognizer.NOT_WHITE, 1));
	}

}
