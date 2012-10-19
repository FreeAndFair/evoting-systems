package org.scantegrity.authoring.invisibleink;

import java.awt.Color;
import java.awt.image.BufferedImage;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.security.SecureRandom;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import javax.imageio.ImageIO;

import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.DocumentException;
import com.itextpdf.text.Image;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.BarcodeQRCode;
import com.itextpdf.text.pdf.BaseFont;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.qrcode.EncodeHintType;
import com.itextpdf.text.pdf.qrcode.ErrorCorrectionLevel;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.BallotRow;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Util;
import org.scantegrity.common.InvisibleInkFactory;

public class PrintableBallotMakerWithBarcodes extends PrintableBallotMaker {
	
	static InvisibleInkFactory iif=null;
	Hashtable<String, Image> textToImage=new Hashtable<String, Image>();
	
	public PrintableBallotMakerWithBarcodes(ElectionSpecification es, BallotGeometry geom) throws Exception {
		super(es, geom);
		
		try {
			SecureRandom c_csprng = SecureRandom.getInstance("SHA1PRNG");
			iif=new InvisibleInkFactory("Tenacity HR192", 16, 3, c_csprng);
/*Rick's settings			
			float[] minMaskColor={0.0f, 0.0f, 0.0f, 0.0f};
			iif.setMinMaskColor(minMaskColor);
			
			float[] maxMaskColor={0.0f, 0.0f, 0.0f, 0.0f};
			iif.setMaxMaskColor(maxMaskColor);
			
			float[] minFontColor={0.4f, 0.0f, 0.65f, 0.0f};
			iif.setMinFontColor(minFontColor);
			
			float[] maxFontColor={0.65f, 0.0f, 0.85f, 0.0f};
			iif.setMaxFontColor(maxFontColor);
			
			float[] minBgColor={0.0f, 0.6f, 0.65f, 0.0f};
			iif.setMinBgColor(minBgColor);
			
			float[] maxBgColor={0.0f, 0.7f, 0.85f, 0.0f};
			iif.setMaxBgColor(maxBgColor);
*/
			//David's Settings UMCP
			//					    C	  M		Y	  K
			float[] minFontColor={0.75f, 0.0f, 0.0f, 0.0f};
			iif.setMinFontColor(minFontColor);
			
			float[] maxFontColor={1.0f, 0.0f, 0.0f, 0.0f};
			iif.setMaxFontColor(maxFontColor);
			
			float[] minBgColor={0.0f, 0.0f, 0.6f, 0.0f};
			iif.setMinBgColor(minBgColor);
			
			float[] maxBgColor={0.0f, 0.0f, 0.85f, 0.0f};
			iif.setMaxBgColor(maxBgColor);
			
			float[] minMaskColor={0.0f, 0.5f, 0.0f, 0.0f};
			iif.setMinMaskColor(minMaskColor);
			
			float[] maxMaskColor={0.0f, 1.0f, 0.0f, 0.0f};
			iif.setMaxMaskColor(maxMaskColor);
			
			//Caution: This can eat up memory quickly.
			iif.setCache(true);
			
			Integer[] p_vGridSize=new Integer[1];
			p_vGridSize[0]=11;

			Integer[] p_vGridSpace=new Integer[1];
			p_vGridSpace[0]=1;

			Integer[] p_hGridSize=new Integer[1];
			p_hGridSize[0]=11;
			
			Integer[] p_hGridSpace=new Integer[1];
			p_hGridSpace[0]=1;
			
			iif.setGrid(p_vGridSize, p_vGridSpace, p_hGridSize, p_hGridSpace);
			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	protected void addSerialNumber(String serial,String prefixForFieldName) {
    	serialFontSize=getFontSize(geom.getSerialTop("0"), helv);//serialFont);
    	
        //step3 - add the serial number in latin
    	Rectangle r=null;
    	
    	//Web Serial Number
    	BallotRow ballotRow=ballotRows.get(Integer.parseInt(serial));
        r=geom.getSerialTop("0");
        drawWhiteRectangle(r);
        String webSerial=ballotRow.getWebSerial();	
        drawRegularText(webSerial, r, this.helv, 12);
        
        // Stub Serial number
	    r=geom.getSerialTop("1");
	    drawWhiteRectangle(r);
	    String printingKey1=ballotRow.getStubSerial();
	    drawRegularText(printingKey1, r, this.helv, 12);
	        	

        //add the 2D barcode		
		r=geom.makeRectangle(geom.getSerialBulletedNode());
	    //drawWhiteRectangle(rect);
		//barcode.setAbsolutePosition(rect.getLeft(),rect.getBottom());
		float w=r.getWidth()*1.25f; 
		float h=r.getHeight()*1.25f;
		float x = r.getLeft()-((w-r.getWidth())/2);
		float y = r.getBottom()-((h-r.getHeight())/2);
		
		try {
		    // Level H is the highest level of error correction. 
		    Map<EncodeHintType, Object> l_hints = 
		    			new Hashtable<EncodeHintType, Object>();
		    l_hints.put( EncodeHintType.ERROR_CORRECTION, 
		    				ErrorCorrectionLevel.H );
			
	        BarcodeQRCode l_barcode = 
								new BarcodeQRCode(ballotRow.getBarcodeSerial(),
	        										(int)Math.max(w,h), 
													(int)Math.max(w,h), 
													l_hints);
	        Image l_img = l_barcode.getImage();
			l_img.setDpi(600, 600);
			l_img.setAbsolutePosition(x, y);
			//l_img.scaleAbsolute(Math.max(w,h), Math.max(w,h));
			cb.addImage(l_img);
		} catch (DocumentException e) {
			e.printStackTrace();
		}
        
    }	
	
	public void addTextCentered(PdfContentByte cb, Rectangle possition, BaseFont font, int XXXfontSize,BaseColor textColor,String text) {
		//draw a white background		
		cb.saveState();
		cb.setColorFill(white);
		cb.setColorStroke(white);
		cb.rectangle(possition.getLeft(), possition.getBottom(), possition.getWidth(), possition.getHeight());
		cb.fillStroke();
		cb.restoreState();
		
		if (mailIn) return;		
		Image l_img=Util.CMYKBufferedImageToCMYKImage(iif.getBufferedImage(" "+text+" "));
		//l_img.setCompressionLevel(9);
		try {
			l_img.setDpi(300, 300);
			l_img.setAbsolutePosition(possition.getLeft(), possition.getBottom());
			l_img.scaleAbsolute(possition.getWidth(), possition.getHeight());
			cb.addImage(l_img);
		} catch (DocumentException e) {
			e.printStackTrace();
		}
		
	}
	
	private void drawRegularText(String text, Rectangle possition,BaseFont font,int fontSize) {
		cb.beginText();
		cb.setFontAndSize(font,fontSize);
		font.correctArabicAdvance();		
		cb.showTextAligned(PdfContentByte.ALIGN_LEFT, text, possition.getLeft(), possition.getBottom(), 0);
		cb.endText();
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) throws Exception {
    	InputConstants.setPublicFolder(InputConstants.publicFolder+"/ward1/");
    	
		ElectionSpecification es=new ElectionSpecification(InputConstants.ElectionSpec);
		BallotGeometry geom=new BallotGeometry(InputConstants.Geometry);

		String background=InputConstants.PdfTemplate;
		String pathToPrintsFile=InputConstants.MeetingTwoPrints;
		
    	PrintableBallotMakerWithBarcodes pbm=new PrintableBallotMakerWithBarcodes(es,geom);
    	//pbm.init(background,pathToPrintsFile);
    	    	
    	int batchSize=10;
    	for (int i=0;i<200;i+=batchSize) {
    		pbm.makePrintableBallots(InputConstants.privateFolder+"", i,i+batchSize-1);
		}
//    	pbm.makePrintableBallots(InputConstants.privateFolder+"", 51,52);
//    	pbm.makePrintableBallots(InputConstants.privateFolder+"", 109,111);
//    	pbm.makePrintableBallots(InputConstants.privateFolder+"", 370,371);
//    	pbm.makePrintableBallots(InputConstants.privateFolder+"", 444,445);
	}

	/**
	 * Make print codes files for the remotegrity system.
	 * @param p_privateFolder
	 * @param p_parseInt
	 * @param p_parseInt2
	 * @throws FileNotFoundException 
	 */
	public void makeRemotegrityBallots(String p_outputFldr, int p_from,
			int p_to) throws FileNotFoundException {
		
		File l_out = new File(p_outputFldr+"/RemotegrityPrintCodes_" 
								+ p_from + "-" + p_to + ".xml");
		makePrintCodesFile(l_out, p_from, p_to);
	}
	
	/**
	 * Make print codes files for the accessibility system.
	 * @param p_privateFolder
	 * @param p_parseInt
	 * @param p_parseInt2
	 * @throws FileNotFoundException 
	 */
	public void makeAccessibilityBallots(String p_outputFldr, int p_from,
			int p_to) throws FileNotFoundException {
		
		File l_out = new File(p_outputFldr+"/AccessibilityPrintCodes_" 
								+ p_from + "-" + p_to + ".xml");
		makePrintCodesFile(l_out, p_from, p_to);
	}

	/**
	 * Make print codes file using the specified name.
	 * @param p_privateFolder
	 * @param p_parseInt
	 * @param p_parseInt2
	 * @throws FileNotFoundException 
	 */
	private void makePrintCodesFile(File p_outFile, int p_from, int p_to) 
	throws FileNotFoundException
	{
		PrintStream l_out = new PrintStream(p_outFile);

		l_out.format("<xml>\n\t<codes>\n");
		
		for (int i = p_from; i <= p_to; i++)
		{
			BallotRow l_b = (BallotRow) ballotRows.get(i);
			String l_ser = l_b.getBarcodeSerial();
			l_out.format("\t\t<ballot barcodeSerial=\"%s\" webSerial=\"%s\" " +
						 "stubSerial=\"%s\">\n", l_ser,
						 l_b.getWebSerial(), l_b.getStubSerial());
			 
			Set<Integer> l_ques = allCodes.get(l_ser).keySet();
			for (Integer l_q : l_ques)
			{
				l_out.format("\t\t\t<question id=\"%d\">\n", l_q);
				Set<Integer> l_codes = allCodes.get(l_ser).get(l_q).keySet();
				for (Integer l_c : l_codes)
				{
					l_out.format("\t\t\t\t<symbol id=\"%d\" code=\"%s\" />\n",
									l_c, allCodes.get(l_ser).get(l_q).get(l_c));	
				}
				l_out.format("\t\t\t</question>\n");
			}
			l_out.format("\t\t</ballot>\n");		
		}
	}
}
