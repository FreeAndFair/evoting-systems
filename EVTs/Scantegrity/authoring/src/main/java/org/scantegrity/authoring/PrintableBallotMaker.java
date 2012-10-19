package org.scantegrity.authoring;

import java.awt.Color;
import java.awt.geom.Point2D;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.StringTokenizer;
import java.util.Vector;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.NodeList;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.DocumentException;
import com.itextpdf.text.Paragraph;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.BaseFont;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.PdfImportedPage;
import com.itextpdf.text.pdf.PdfLayer;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfWriter;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.Cluster;
import org.scantegrity.common.ContestSymbols;
import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

public class PrintableBallotMaker {

	BallotGeometry geometry;
	protected Question[] qs=null;
	ContestSymbols contestSymbols;

	private PdfContentByte cb = null;
	private PdfReader backgroundReader = null;
	Rectangle pdfPageSize = null;
	
	protected BaseFont helv = null;
	protected BaseFont serialFont=null;
	protected static String serialFontPath="TENHB192.TTF";
	
    int serialSize = 18;
   	int wingdingsSize = 32;	
    int symbolFontSize = 14;
    
    String fileNamePrefix="";
    
    int batchSize=125;
    
    float pdfPageheight=0;
    
	public PrintableBallotMaker(String pathToBallotMap,String pathToprintsFile, String pathToElectionSpec) throws Exception {
		setDefaults(pathToprintsFile,pathToElectionSpec);		
		Document doc=Util.DomParse(pathToBallotMap);
		setUp(doc, pathToprintsFile, pathToElectionSpec);
		geometry = new BallotGeometry(pathToBallotMap);
	}
		
	private void createBlankBackgroundPage(float w,float h) {
		com.itextpdf.text.Document document = new com.itextpdf.text.Document(new Rectangle(w,h));
		pdfPageheight=h;
		try {
			PdfWriter.getInstance(document,new FileOutputStream("__BlankPdf.pdf"));
			document.open();
			document.add(new Paragraph(" "));
		} catch (DocumentException de) {
			System.err.println(de.getMessage());
		} catch (IOException ioe) {
			System.err.println(ioe.getMessage());
		}
		document.close();
		try {
			backgroundReader = new PdfReader("__BlankPdf.pdf");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public void make(int start,int stop, Prow.ChosenPage page, String getPathToWatermark, boolean coloredWatermark, boolean withHoleCircles, boolean withVotes, String outputDir) throws Exception {				
		try {
			backgroundReader = new PdfReader(getPathToWatermark);
			pdfPageSize = backgroundReader.getPageSize(1);
			pdfPageheight=pdfPageSize.getHeight();
			if (coloredWatermark) {
				backgroundReader = new PdfReader(coverAllColor(getPathToWatermark));
				//TODO modify the background to cover all the colors
			}
			if (withHoleCircles) {
				//TODO modify the background to show the holle circles
			}
		} catch (Exception e) {
			createBlankBackgroundPage(geometry.getWidth(),geometry.getHeight());
		}
		
		File f= new File(outputDir);
		if (!f.exists())
			f.mkdirs();		
		make(outputDir,start,stop,page,withVotes);		
	}
	
	
	private void make(String outputDir,int start,int stop,Prow.ChosenPage page,boolean withVotes) throws Exception {       
		com.itextpdf.text.Document document = new com.itextpdf.text.Document(pdfPageSize);
		pdfPageheight=pdfPageSize.getHeight();
		File f= new File(outputDir+"/"+fileNamePrefix+page+"_"+start+".pdf");
		PdfWriter writer = PdfWriter.getInstance(document,new FileOutputStream(f));
		writer.setPdfVersion(PdfWriter.VERSION_1_5);
		writer.setViewerPreferences(PdfWriter.PageModeUseOC);
		
		document.open();
        cb = writer.getDirectContent();
        
		PdfLayer l1 = new PdfLayer(""+start+page, writer);
		cb.beginLayer(l1);
        
		PdfImportedPage page1 = writer.getImportedPage(backgroundReader, 1);

    	symbolFontSize=FormMaker.getFontSize(geometry.getTop("0","0"),helv);
		
        int batchNumber = 0;
        int numberOfPrintedBallotsInThisBatch=0;
		for (int i=start;i<=stop;i++) {
        	if (numberOfPrintedBallotsInThisBatch >= batchSize) {
        		document.close();
                batchNumber++;
                numberOfPrintedBallotsInThisBatch=0;
        		document = new com.itextpdf.text.Document(pdfPageSize);
        		f= new File(outputDir+"/"+fileNamePrefix+page+"_"+(start+batchNumber*batchSize)+".pdf");
        		writer = PdfWriter.getInstance(document, new FileOutputStream(f));
        		document.open();      
                cb = writer.getDirectContent();

				page1 = writer.getImportedPage(backgroundReader, 1);
        	}
            cb.addTemplate(page1,0,0);        	
        	document.setMargins(0,0,0,0);        	
				        
			drawAlignmentMarks(geometry.makeRectangle(geometry.getUpperAlignment()));
			drawAlignmentMarks(geometry.makeRectangle(geometry.getLowerAlignment()));
			
			if (page.equals(Prow.ChosenPage.TOP) || page.equals(Prow.ChosenPage.BOTH))
				addSerial(Util.AddleadingZeros(i+"", geometry.getNoDigitsInSerial()), geometry.getSerialTopClusters());
			if (page.equals(Prow.ChosenPage.BOTTOM) || page.equals(Prow.ChosenPage.BOTH))
				addSerial(Util.AddleadingZeros(i+"", geometry.getNoDigitsInSerial()), geometry.getSerialBottomClusters());
			
			//TODO add colors
			addContests(i,page,withVotes);
			
			numberOfPrintedBallotsInThisBatch++;			
			if (numberOfPrintedBallotsInThisBatch < batchSize && i< stop) {
	        	document.newPage();
			}			
        }
		cb.endLayer();
		document.close();
	}

	public void addSerial(String serialString, Vector<Cluster> serialMap) {
		String text="";
		for (int i=0;i<serialMap.size();i++) {
			Cluster serialDigit = serialMap.get(i);
			text = Character.toString(serialString.charAt(i));			
			drawTextCenter(text, serialDigit.getCenterOfMass(), serialFont, serialSize);
		}		
	}
	
    protected void addContests(int i, Prow.ChosenPage page, boolean withVotes) throws Exception {
    	String[] allSymbolsTop= contestSymbols.getAllSymbols(i,0);
    	String[] allSymbolsBottom=contestSymbols.getAllSymbols(i,1);    	
    	int noRanks=1;
    	int allSymbolsPos=0;
        //step3 - for each race, add the placeholders for symbols
        for (int qno=0;qno<qs.length;qno++) {        	
        	//step 3.1 add the top symbols
        	//for each candidate
            noRanks=1;
            if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)
            	noRanks=qs[qno].getMax();
            for (int rank=0;rank<noRanks;rank++) {                	            		        	
	        	for (int ano=0;ano<qs[qno].getAnswers().size();ano++) {        		
        			if (withVotes) {
        				if (Math.random() < 1.0d/(double)qs[qno].getAnswers().size()) {
        					drawVote(geometry.getBottomCluster(qno+"", rank+"", ano+""), page);
        				}
        			}
	        		
	        		if (page.equals(Prow.ChosenPage.TOP) || page.equals(Prow.ChosenPage.BOTH))
	        			drawTextCenter(allSymbolsTop[allSymbolsPos], geometry.getTopCluster(qno+"",0+"",ano+"").getCenterOfMass(),helv, symbolFontSize);
                	if (page.equals(Prow.ChosenPage.BOTTOM) || page.equals(Prow.ChosenPage.BOTH))
                		drawTextCenter(allSymbolsBottom[allSymbolsPos], geometry.getBottomCluster(qno+"",rank+"",ano+"").getCenterOfMass(),helv, symbolFontSize);
        			allSymbolsPos++;
	        	}
	        	allSymbolsPos-=qs[qno].getAnswers().size();
        	}
            allSymbolsPos+=qs[qno].getAnswers().size();
        }
    }

	private void drawAlignmentMarks(Rectangle rect) {
//Amir editing
			//cb.setColorStroke(new BaseColor(Color.BLACK));
			cb.setColorStroke(new BaseColor(0,0,0));
			//cb.setColorFill(new BaseColor(Color.BLACK));
			cb.setColorStroke(new BaseColor(0,0,0));
			
			float hh = rect.getHeight();
			float w = rect.getWidth();
	        float l=w>hh?hh:w;
	        cb.circle(rect.getLeft()+w/2,rect.getBottom()+hh/2,l/2);
			cb.fill();
			//cb.circle((float)(p.getX()*72),(float)(h-p.getY()*72),geometry.getHoleDiameter()*72/2);
			cb.fillStroke();
	}
		
	private void setDefaults(String pathToprintsFile,String pathToElectionSpec) throws Exception {
		Color[] colors = new Color[1];
		colors[0]= Color.BLACK;		
		
		Color[] colorPallete=new Color[1];
		colorPallete[0] = Color.BLACK;
		contestSymbols = new ContestSymbols(pathToprintsFile,pathToElectionSpec,ContestSymbols.alphabet,true);
		
		helv = BaseFont.createFont("Helvetica", BaseFont.CP1252, BaseFont.EMBEDDED);
		serialFont = BaseFont.createFont(getClass().getResource(serialFontPath).toString(), BaseFont.CP1252, BaseFont.EMBEDDED);
		qs=new ElectionSpecification(pathToElectionSpec).getOrderedQuestions();
	}
	
	private void setUp(Document doc,String pathToPrintsFile,String pathToElectionSpec) {
		
		try {
			NamedNodeMap contestsAttr = doc.getElementsByTagName("contests").item(0).getAttributes();
	
			StringTokenizer allChars = new StringTokenizer(contestsAttr.getNamedItem("symbols").getNodeValue());
			Vector<String> allCharsVector=new Vector<String>();
			while (allChars.hasMoreTokens())
				allCharsVector.add(allChars.nextToken());
			String[] chars=new String[allCharsVector.size()];
			int pos=0;
			for (String s:allCharsVector)
				chars[pos++]=s;
			
			
			String resetString = contestsAttr.getNamedItem("reset").getNodeValue();
			boolean reset=true;
			if (resetString.toLowerCase().compareTo("yes") == 0)
				reset = true;
			else
				reset = false;

			boolean colorPalletReset = true;
			try {
				if (doc.getElementsByTagName("colorPallete").item(0).getAttributes().getNamedItem("reset").getNodeValue().toLowerCase().compareTo("yes") == 0)
					colorPalletReset = true;
				else
					colorPalletReset = false;
			} catch (Exception e) {
				
			}				
			
			NodeList colorList = doc.getElementsByTagName("color");
			Color[] colorPallete = new Color[colorList.getLength()];
			for (int i=0;i<colorList.getLength();i++) {
				colorPallete[i]=new Color(Integer.parseInt(colorList.item(i).getAttributes().getNamedItem("value").getNodeValue(),16));		
			}
		
			
			contestSymbols = new ContestSymbols(pathToPrintsFile,pathToElectionSpec,chars,reset);		
		} catch (Exception e) {
			
		}		
	}
	
	private void drawVote(Cluster serialDigit,Prow.ChosenPage page) {
		Point2D p = serialDigit.getCenterOfMass();
//Amir editing	
		//cb.setColorFill(new BaseColor(Color.ORANGE));
		cb.setColorFill(new BaseColor(255,128,0));
		//cb.setColorStroke(new BaseColor(Color.ORANGE));
		cb.setColorFill(new BaseColor(255,128,0));
		float radius = (float)((Math.max((serialDigit.getXmax()-serialDigit.getXmin()),(serialDigit.getYmax()-serialDigit.getYmin()))*1.1 / 2));
		if (page.equals(Prow.ChosenPage.BOTTOM))
			radius*=0.7;
		cb.circle((float)(p.getX()*72),(float)(pdfPageheight-p.getY()*72),radius*72);
		cb.fillStroke();
		if (page.equals(Prow.ChosenPage.TOP)) {
//Amir editing
			//cb.setColorFill(new BaseColor(Color.WHITE));
			cb.setColorFill(new BaseColor(255,255,255));
			//cb.setColorStroke(new BaseColor(Color.WHITE));
			cb.setColorFill(new BaseColor(255,255,255));
			radius*=0.7;
			cb.circle((float)(p.getX()*72),(float)(pdfPageheight-p.getY()*72),radius*72);
			cb.fillStroke();
		}
		cb.setRGBColorFill(0,0,0);
	}	
		
	private void drawTextCenter(String text,Point2D p,BaseFont font,int fontSize) {
		cb.beginText();
		cb.setFontAndSize(font,fontSize);
		float yoffset = (font.getAscentPoint(text,fontSize)+font.getDescentPoint(text,fontSize)) / 2;
		font.correctArabicAdvance();
		cb.showTextAligned(PdfContentByte.ALIGN_CENTER, text, (float)(p.getX()*72),(float)(pdfPageheight-p.getY()*72-yoffset),0);
		cb.endText();
	}
	
	public String getFileNamePrefix() {
		return fileNamePrefix;
	}

	public void setFileNamePrefix(String fileNamePrefix) {
		this.fileNamePrefix = fileNamePrefix;
	}

	private String coverAllColor(String getPathToWatermark) throws Exception {
		String cleanBackground=getPathToWatermark+".temp";
		com.itextpdf.text.Document document = new com.itextpdf.text.Document(pdfPageSize);

		File f= new File(cleanBackground);
		PdfWriter writer = PdfWriter.getInstance(document,new FileOutputStream(f));
		writer.setPdfVersion(PdfWriter.VERSION_1_5);
		writer.setViewerPreferences(PdfWriter.PageModeUseOC);
		
		document.open();
        cb = writer.getDirectContent();

		PdfImportedPage page1 = writer.getImportedPage(backgroundReader, 1);
        cb.addTemplate(page1,0,0);        	
    	document.setMargins(0,0,0,0);        	
					
		FormMaker.drawWhiteRectangleStatic(cb, geometry.makeRectangle(geometry.getUpperAlignment()));
		FormMaker.drawWhiteRectangleStatic(cb, geometry.makeRectangle(geometry.getLowerAlignment()));

		
		Rectangle r=null;
        for (int i=0;i<geometry.getNoDigitsInSerial();i++) {
        	r=geometry.getSerialTop(i+"");
        	FormMaker.drawWhiteRectangleStatic(cb,r);
            
            r=geometry.getSerialBottom(i+"");
            FormMaker.drawWhiteRectangleStatic(cb,r);
        }
		
    	int noRanks=1;
        for (int qno=0;qno<qs.length;qno++) {        	
        	for (int ano=0;ano<qs[qno].getAnswers().size();ano++) {
        		r = geometry.getTop(qno+"",ano+"");
        		FormMaker.drawWhiteRectangleStatic(cb,r);
                noRanks=1;
                if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)
                	noRanks=qs[qno].getMax();
                for (int rank=0;rank<noRanks;rank++) {                	
                	r = geometry.getBottom(qno+"",rank+"",ano+"");                	
                	FormMaker.drawWhiteRectangleStatic(cb,r);
                }
        	}
        }
		document.close();
        
        return cleanBackground;
	}
	
	public static void main(String[] args) throws Exception {
		String dir="Elections/VoComp/";
		PrintableBallotMaker pbm=new PrintableBallotMaker(dir+"geometry.xml",dir+"MeetingTwoPrints.xml",dir+"ElectionSpec.xml");
		pbm.make(1,5, Prow.ChosenPage.BOTTOM, dir+"VoComp Sample ballot PunchScan.pdf",true,false,true,dir);
	}
}
