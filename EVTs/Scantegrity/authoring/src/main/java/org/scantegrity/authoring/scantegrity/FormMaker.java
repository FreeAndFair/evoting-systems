package org.scantegrity.authoring.scantegrity;

import java.awt.Color;
import java.io.FileOutputStream;
import java.io.IOException;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.DocumentException;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.AcroFields;
import com.itextpdf.text.pdf.BaseFont;
import com.itextpdf.text.pdf.PdfAction;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfStamper;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Util;

public class FormMaker extends org.scantegrity.authoring.FormMaker {

	protected BaseFont barcodeFont=null;
	protected BaseFont bulletedFont=null;
	
	protected int barcodeFontSize = 14;
	protected int bulletedTopFontSize = 8;
	
	static {
		//serialFontPath=".."+Util.fileSeparator+"TENHB192.TTF";
	}
	
	public FormMaker(ElectionSpecification es,BallotGeometry geom) throws Exception {
		super(es,geom);
		bulletedFont=BaseFont.createFont(getClass().getResource("WINGDNG2.TTF").toString(), BaseFont.CP1252, BaseFont.EMBEDDED);		
		barcodeFont=BaseFont.createFont(getClass().getResource("FREE3OF9.TTF").toString(), BaseFont.CP1252, BaseFont.EMBEDDED);
	}
	
	public void make(String background, String outFile) throws DocumentException, IOException {
		String outFileTemp=outFile+".temp";
		super.make(background, outFileTemp);
		
		//fill in the bulletedserial number
		PdfReader reader = new PdfReader(outFileTemp);
		
		PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(outFile));
		
		int zero=105;
			
        AcroFields form1 = stamp1.getAcroFields();
        for (int row=0;row<geom.getNoDigitsInSerial();row++) {
        	for (int digit=0;digit<10;digit++) {
        		form1.setField("serialBulleted_"+row+"_"+digit,Character.toString(new Character((char)(zero+digit))));
        	}
        }
        stamp1.close();
	}
    
	protected void addSerialNumber(String serial,String prefixForFieldName) {
    	serialFontSize=getFontSize(geom.getSerialTop("0"), helv);//serialFont);
    	
        //step3 - add the serial number in latin
    	Rectangle r=null;
        for (int i=0;i<geom.getNoDigitsInSerial();i++) {
        	r=geom.getSerialTop(i+"");
        	
        	drawWhiteRectangle(r);
        	
        	pdfFormField = makeText(
        			r, 
        			prefixForFieldName+"serialTop_"+i,
            		helv,//serialFont,
            		serialFontSize,
            		Character.toString(serial.charAt(i)));
            writer.addAnnotation(pdfFormField);
        }
        
        //add the serial number in barcode
        r=geom.getSerialBarcode();
        if (r!=null) {
	    	barcodeFontSize=getFontSize(r, Util.AddleadingZeros("", geom.getNoDigitsInSerial()),barcodeFont);	    	
	    	drawWhiteRectangle(r);
        
	    	pdfFormField = makeText(
	    			r, 
	        		prefixForFieldName+"serialBarcode",
	        		barcodeFont,
	        		barcodeFontSize,
	        		serial);
	       writer.addAnnotation(pdfFormField);
        }
        
        if (true) return;

/*        cb.saveState();
        cb.setColorStroke(Color.BLACK);
        cb.setColorFill(Color.YELLOW);
        cb.setLineDash(6,0);
        cb.rectangle(72*(8.5f-1.6f),-1, 72*1.7f, 72*0.8f);
        
        cb.moveTo(72*8.5f, 72*0.8f);
        cb.lineTo(72*(8.5f-1.6f), 72*0.8f);
        cb.lineTo(72*(8.5f-1.6f), 0);
        cb.fillStroke();//.stroke();
        cb.restoreState();
*/        
        //add the serial number bulleted.
        Rectangle[][] allSerialNumberBullets=geom.getSerialBulleted();
        bulletedTopFontSize=getFontSize(allSerialNumberBullets[0][0], bulletedFont);
        char bullet=162;
        for (int row=0;row<allSerialNumberBullets.length;row++) {
        	for (int digit=0;digit<allSerialNumberBullets[row].length;digit++) {
        		r=allSerialNumberBullets[row][digit];
        		
        		drawWhiteRectangle(r);
        		
        		if (Character.toString(serial.charAt(row)).equals(digit+"")) {
        			BaseColor temp=symbolColor;//new Color(symbolColor.getRGB());
        			symbolColor=black;
    	        	pdfFormField = makeText(
    	        			r, 
    	            		prefixForFieldName+"serialBulleted_"+row+"_"+digit,
    	            		bulletedFont,
    	            		bulletedTopFontSize,
    	            		Character.toString(bullet));
        			symbolColor=temp;
        		}
        		else {
    	        	pdfFormField = makeText(
    	        			r, 
    	            		prefixForFieldName+"serialBulleted_"+row+"_"+digit,
    	            		bulletedFont,
    	            		bulletedTopFontSize,
    	            		Character.toString(new Character((char)(105+digit))));
        		}
        		
	        	//pdfFormField.setValueAsString(digit+"");
	            writer.addAnnotation(pdfFormField);
        	}
        }
    }	

	protected void addContests(String[] allSymbolsTop,String[] allSymbolsBottom,String prefixForFieldName) {
    	symbolTopFontSize=getFontSize(geom.getTop("0","0","0"),helv);
    	
        String sufix;
    	
    	String func="";
    	int noRanks=1;
    	int allSymbolsPos=0;
        //step3 - for each race, add the placeholders for symbols
        for (int qno=0;qno<qs.length;qno++) {        	
        	//step 3.1 add the top symbols
        	//for each candidate
        	for (int c=0;c<qs[qno].getAnswers().size();c++) {
        		sufix = "_"+qno+"_"+c;                
            	//step 3.2 for each row (rank), add the bottom symbols and the orange (top, bottom and both)
                noRanks=1;
                if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)
                	noRanks=qs[qno].getMax();
                for (int rank=0;rank<noRanks;rank++) {
                	sufix = "_"+qno+"_"+rank+"_"+c;
                	rect = geom.getTop(qno+"",rank+"",c+"");

                	drawWhiteRectangle(rect);
                	
                	pdfFormField = makeButtonTopHoles(
                			rect, 
                    		"topHole"+sufix);
                    writer.addAnnotation(pdfFormField);                	                    
                                        
                	pdfFormField = makeButtonOrangeBoth(
                			rect, 
                    		"orangeBoth"+sufix);
                    writer.addAnnotation(pdfFormField);                    
                                        
                    //put the symbols to the left of the oval. if you put them
                    //in the oval, and the symbol have lots of black, it may get
                    //detected as marked. Plus the voters sees the letter after marking
                    if (rank==0) {
	                	pdfFormField = makeText(
	                			translate(rect, 0-rect.getWidth(),0), 
	                    		prefixForFieldName+"bottomSymbol"+sufix,
	                    		helv,
	                    		symbolTopFontSize,
	                    		allSymbolsTop[allSymbolsPos]);
	                    writer.addAnnotation(pdfFormField);
                    }
                    
                	pdfFormField = makeButtonVoteBottom(
                			rect, 
                    		"voteBottom"+sufix);
        			if (qs[qno].getTypeOfAnswer().compareTo(Constants.ONE_ANSWER)==0)
        				func="voteOne("+qno+","+c+");";
        			else
        				if (qs[qno].getTypeOfAnswer().compareTo(Constants.MULTIPLE_ANSWERS)==0)
        					func="voteMany("+qno+","+c+");";
        				else
        					if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)					
        						func="voteRank("+qno+","+rank+","+c+");";
                	pdfFormField.setAction(PdfAction.javaScript(func, writer));
                    writer.addAnnotation(pdfFormField);                    
                }
                allSymbolsPos++;
        	}
        }
    }
    
    protected void addFinishButtons() {
    	
    }
    
    public static Rectangle translate(Rectangle rect,float tx,float ty) {
    	float fromx=rect.getLeft()+tx;
    	float fromy=rect.getBottom()+ty;
    	float tox=rect.getRight()+tx;
    	float toy=rect.getTop()+ty;
    	return new Rectangle(fromx,fromy,tox,toy);
    }
    
	public static void main(String args[]) throws Exception {
		String dir=InputConstants.publicFolder;
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");
		BallotGeometry geom = new BallotGeometry(dir+"geometry.xml");
		FormMaker fm = new FormMaker(es,geom);
		String background=dir+"TP2007 1D bardoce.pdf";
		String outFile=dir+"javaCreatedForm.pdf";
		fm.make(background, outFile);
	}    
}
