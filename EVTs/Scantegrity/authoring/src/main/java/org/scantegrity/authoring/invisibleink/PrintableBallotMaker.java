package org.scantegrity.authoring.invisibleink;

import java.awt.Color;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.TreeMap;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.BallotRow;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.InvisibleInkCodes;
import org.scantegrity.common.Util;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.Document;
import com.itextpdf.text.DocumentException;
import com.itextpdf.text.Paragraph;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.BaseFont;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.PdfGState;
import com.itextpdf.text.pdf.PdfImportedPage;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfWriter;

public class PrintableBallotMaker extends org.scantegrity.authoring.scantegrity.PrintableBallotMaker {
	
	private PdfReader backgroundReader = null;
	ElectionSpecification es=null;
	TreeMap<String,TreeMap<Integer,TreeMap<Integer,String>>> allCodes=null;
	TreeMap<Integer, BallotRow> ballotRows=null;
	
	static String BarChar="|";
	//80%static Color dummyInvisibleInkColor=new Color(255,255,2);
	//static Color dummyInvisibleInkColor=new Color(255,255,153);//40% Yellow
	//static Color dummyInvisibleInkColor=new Color(230,255,102);//60% Yellow 10%Cyan	
	//static Color dummyInvisibleInkColor=new Color(153,255,102);//60% Yellow 40%Cyan
	//static Color dummyInvisibleInkColor=new Color(0,255,0);//100% Yellow 100%Cyan
	static BaseColor ovalColor=new BaseColor(255,0,255);//100% Yellow
	//static Color dummyInvisibleInkColor=new Color(255,255,128);//50% Yellow
	//static Color dummyInvisibleInkColor=new Color(255,255,204);//20% Yellow
	//static Color dummyInvisibleInkColor=new Color(255,255,102);//60% Yellow
	//static Color dummyInvisibleInkColor=new Color(255,255,77);//70% Yellow
	//static Color dummyInvisibleInkColor=new Color(255,255,51);//70% Yellow
	//static Color ovalColor=new Color(0,255,255);//100% Cyan
	
	//static Color contourColor=Color.BLACK;
	//static Color contourColor=new Color(102,102,102);//60%
	//static Color contourColor=new Color(128,128,128);//50%
	
	static float opacity=1f;//0.8f;//0.4f;
	
	//static Color decoyCodesColor=new Color(0,255,255);
	static BaseColor decoyCodesColor=new BaseColor(255,0,255);//Magenta
	//static Color decoyCodesColor=new Color(0,255,255);//Cyan
	static float decoyOpacity=0.14f;
	
	static String[] dummyBackgrounds={"!","\"","#","$","%","&","'","(",")"}; 
	    
	static private String allDecoyCodes="";
	
	public boolean mailIn=false;
	
	public PrintableBallotMaker(ElectionSpecification es,BallotGeometry geom) throws Exception {
		super(es,geom);
		this.es=es;
		
		//80%symbolColor=new Color(255,48,255);
		//symbolColor=new Color(255,153,255);//40% Magenta
		//symbolColor=new Color(230,102,255);//60% Magenta 10%Cyan
		//symbolColor=new Color(153,102,255);//60% Magenta 40%Cyan
		//symbolColor=new Color(0,0,255);//100% Magenta 100%Cyan
		symbolColor=new BaseColor(0,255,255);//100% Magenta
		//symbolColor=new Color(255,255,0);//100% Yellow
		//symbolColor=new Color(255,128,255);//50% Magenta
		//symbolColor=new Color(255,102,255);//60% Magenta
		//symbolColor=new Color(255,204,255);//20% Magenta
		//symbolColor=new Color(128,255,255);//50% CYAN
		//symbolColor=new Color(255,77,255);//70% Magenta
		//symbolColor=new Color(255,51,255);//80% Magenta
		//symbolColor=Color.WHITE;
		//symbolColor=new Color(255,128,255);//50% Magenta
		//symbolColor=Color.BLACK;
	}
	
	protected void loadJavaScript() throws IOException {
		//writer.addJavaScript("app.alert(\"The codes are \");");	
	}
	
	public void init(String background,String pathToPrintsFile) throws Exception {
		try {
			backgroundReader = new PdfReader(background);
		} catch (Exception e) {
			createBlankBackgroundPage(geom.getWidth()*72,geom.getHeight()*72);
		}
		
		org.w3c.dom.Document doc=Util.DomParse(pathToPrintsFile);
		allCodes=new TreeMap<String, TreeMap<Integer,TreeMap<Integer,String>>>();
		ballotRows=new TreeMap<Integer, BallotRow>();
		
		String printedSerial=null;
		int qid=-1;
		int sid=-1;
		NodeList ballots=doc.getElementsByTagName("ballot");
		for (int b=0;b<ballots.getLength();b++) {
			BallotRow ballotRow=new BallotRow(ballots.item(b));
//System.out.println("b="+b+" ballotRow="+ballotRow);			
			printedSerial=ballotRow.getBarcodeSerial();
			ballotRows.put(b, ballotRow);
			
			TreeMap<Integer,TreeMap<Integer,String>> ballotCodes=new TreeMap<Integer, TreeMap<Integer,String>>();
			for (Node question=ballots.item(b).getFirstChild();question!=null;question=question.getNextSibling()) {
				if (question.getNodeName().compareTo("question")==0) {
					qid=Integer.parseInt(question.getAttributes().getNamedItem("id").getNodeValue());
					TreeMap<Integer, String> questionCodes=new TreeMap<Integer, String>();
					for (Node symbol=question.getFirstChild();symbol!=null;symbol=symbol.getNextSibling()) {
						if (symbol.getNodeName().compareTo("symbol")==0) {
							sid=Integer.parseInt(symbol.getAttributes().getNamedItem("id").getNodeValue());
							questionCodes.put(sid, symbol.getAttributes().getNamedItem("code").getNodeValue());
						}
					}
					ballotCodes.put(qid, questionCodes);
				}
			}
			allCodes.put(printedSerial, ballotCodes);
		}
//System.out.println(allCodes);
	}
	
	public void makePrintableBallots(String outputDir,int start,int stop) throws Exception {
		//We are going to need all available memory.
        System.gc();
		Rectangle pdfPageSize = backgroundReader.getPageSize(1);
		//double scalling = pdfPageSize.getWidth() / ballotMap.getW();
		
		Document document = new Document(pdfPageSize);
		File f = new File(outputDir+"/"+start+"-"+stop+".pdf");
		writer = PdfWriter.getInstance(document,new FileOutputStream(f));
		writer.setPdfVersion(PdfWriter.VERSION_1_4);
		writer.setPDFXConformance(PdfWriter.PDFXNONE);//.PDFX32002);
		writer.setFullCompression();
		
		document.open();
        cb = writer.getDirectContent();
        
		PdfImportedPage page1 = writer.getImportedPage(backgroundReader, 1);
		
		document.setMargins(0,0,0,0);
		cb.addTemplate(page1,0,0);


		//start--;
		//stop--;
		
		for (int i=start;i<=stop;i++) {
			//long l_d1 = System.currentTimeMillis();
			addAlignment(i+"");
			addSerialNumber(i+"",i+"");			
			addContests(ballotRows.get(i).getBarcodeSerial());
			if (i!=stop) {
				document.newPage();
				cb.addTemplate(page1,0,0);
			}
			//System.out.format("GenTime %d\n", System.currentTimeMillis()-l_d1);
		}
		/*
		document.newPage();
		document.add(new Paragraph("The decoy codes are: "));
		document.add(new Paragraph(allDecoyCodes));
		*/
		document.close();
        //System.gc();
	}
	
	protected void addOval(PdfContentByte cb, Rectangle possition) {
		if (possition.getHeight()>possition.getWidth()) {
			System.err.println("Cannot draw jelly bean; the height is greater then the widtd for "+possition);
			return;
		}
		float width=1f;
		//float width=0.9f;
		
		//draw a thicker white line
		//float widthWhite=possition.getHeight()*0.22f;
		float widthWhite=possition.getHeight()*0.32f;
		cb.saveState();
		{
			PdfGState state=new PdfGState();
			state.setStrokeOpacity(1f);
			cb.setGState(state);
		}		
		cb.setCMYKColorStrokeF(0,0,0,0);
		cb.setLineWidth(widthWhite);
		cb.roundRectangle(possition.getLeft()-widthWhite/2, possition.getBottom()-widthWhite/2, possition.getWidth()+widthWhite, possition.getHeight()+widthWhite, possition.getHeight()/2+widthWhite/2);
		cb.stroke();
		cb.restoreState();

		//draw the jelly bean itself
		cb.saveState();
		{
			PdfGState state=new PdfGState();
			state.setStrokeOpacity(1f);
			cb.setGState(state);
		}		
		cb.setCMYKColorStrokeF(0,0,0,0);
		cb.setLineWidth(width);
		cb.roundRectangle(possition.getLeft(), possition.getBottom(), possition.getWidth(), possition.getHeight(), possition.getHeight()/2);
		cb.stroke();
		cb.restoreState();

		cb.saveState();
		{/*
			PdfGState state=new PdfGState();
			state.setStrokeOpacity(0.6f);
			cb.setGState(state);
			*/
		}
		cb.setCMYKColorStrokeF(0,0,0,0.5f);
		cb.roundRectangle(possition.getLeft(), possition.getBottom(), possition.getWidth(), possition.getHeight(), possition.getHeight()/2);
		cb.stroke();		
		cb.restoreState();		
	}
/*	
	public static int getNoBars(BaseFont serialFont, int symbolTopFontSize,float width) {
    	StringBuffer bars=new StringBuffer("");
    	float wc=0;
       	do {
    		wc=Math.abs(serialFont.getWidthPoint(bars.toString(),symbolTopFontSize));
    		bars.append("|");
    	} while (wc<width);
       	return bars.toString().length();
	}
*/	
	protected void addContests(String printedSerial) {
		rect=geom.getTop("0","0","0");
    	symbolTopFontSize=getFontSize(rect,"O",serialFont);
    	//symbolTopFontSize=getFontSize(rect,BarChar,serialFont);

    	//if (true) return;
    	
    	int allSymbolsPos=0;
    	int noRanks=0;
        //step3 - for each race, add the placeholders for symbols
        for (int qno=0;qno<qs.length;qno++) {        	
        	//step 3.1 add the top symbols
        	//for each candidate
        	allSymbolsPos=0;
        	for (int c=0;c<qs[qno].getAnswers().size();c++) {                
            	//step 3.2 for each row (rank), add the bottom symbols and the orange (top, bottom and both)
                noRanks=1;
                if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)
                	noRanks=qs[qno].getMax(); 
        		for (int rank=0;rank<noRanks;rank++) {
                	rect = geom.getTop(qno+"",rank+"",c+"");
                	
                	allDecoyCodes+="Contest number "+qno+" answer number"+c+" rank "+rank+"\n";
                	
//System.out.println(qno+" "+rank+" "+c);
//System.out.println(printedSerial+" "+qno+" "+allSymbolsPos);
//System.out.println(allCodes.get(printedSerial).get(qno).get(allSymbolsPos));                	
                	
                	//addTextCentered(cb,rect,serialFont,symbolTopFontSize,symbolColor,allCodes.get(printedSerial).get(qno).get(allSymbolsPos));
                	
                	addTextCentered(cb,rect,serialFont,14,symbolColor,allCodes.get(printedSerial).get(qno).get(allSymbolsPos));
                	addOval(cb,rect);
                	allSymbolsPos++;
                }
        	}
        }
    }

	public void addTextCentered(PdfContentByte cb, Rectangle possition, BaseFont font, int XXXfontSize,BaseColor p_symbolColor,String text) {
		//draw a white background
		//FIXME - now we have a fixed size font, based on the size of the oval 0.38 X 0.13 inches in the definition file
		int fontSize=XXXfontSize;//11;//getFontSize(possition,text,font);
//Amir editing		
		//BaseColor l_white = new BaseColor(Color.WHITE);
		BaseColor l_white = new BaseColor(255,255,255);		
		cb.saveState();
		cb.setColorFill(l_white);
		cb.setColorStroke(l_white);
		cb.rectangle(possition.getLeft(), possition.getBottom(), possition.getWidth(), possition.getHeight());
		cb.fillStroke();
		cb.restoreState();
		
		float rectLeft=possition.getLeft();
		float rectBottom=possition.getBottom();
		
		float textWidthPoints=Math.abs(font.getWidthPoint(text,fontSize));
		float textHeigthPoints=Math.abs(font.getAscentPoint(text,fontSize));//+Math.abs(font.getDescentPoint(text,fontSize));


		//check how many | charachters fit in the xoffset
		float barWidth=Math.abs(font.getWidthPoint(BarChar,fontSize));//*0.995f;		
		//int noBarsBeforeText=(int)(xoffset / barWidth +0.0f);
		//float xDummyInk=xCode-noBarsBeforeText*barWidth;
		//StringBuffer bars=new StringBuffer("");
		//for (int i=0;i<=(int)(possition.getWidth()/barWidth);i++) {
			//bars.append(BarChar);
			//System.out.println(Math.abs(font.getWidthPoint(bars.toString(),fontSize)));
		//}
		
//		System.out.println("barWidth="+barWidth+" allBarsWidth="+Math.abs(font.getWidthPoint(bars.toString(),fontSize)));
		
		float xBar=rectLeft;
		float yBar=rectBottom+(possition.getHeight()-textHeigthPoints)/2;
		
		//float xoffset=(possition.getWidth()-textWidthPoints)/2;
		int noTotalPixels=Math.round((possition.getWidth()/barWidth));
		int noPixelsTheTextIsWide=Math.round((Math.abs(font.getWidthPoint(text,fontSize))/barWidth));

		//this offset is calculated depending on the size of the text 
		int randomOffset=2+(int)(Math.random()*Math.max(0,((noTotalPixels-noPixelsTheTextIsWide)-4)));
		
		//int randomOffset=(3+(int)(Math.random()*4));
		//float xCode=xBar+randomOffset*barWidth;
//System.out.println("xBar="+xBar+" randomOffset="+randomOffset+" barWidth="+barWidth+" xCode="+xCode);		
		//float yCode=yBar;		

//System.out.println("xBar="+xBar+" yBar="+yBar+" xCode="+xCode+" yCode="+yCode+" barWidth="+barWidth);		

		//draw the DUMMY invizible ink
		//draw the first pixels as bars 
//System.out.println(Math.round((possition.getWidth()/barWidth))+" "+(possition.getWidth()/barWidth));		
		int noPixelsSoFar=0;
		float x=xBar,y=yBar;
		String t=null;
		for (int i=0;i<randomOffset;i++) {
			cb.saveState();
			{
				PdfGState state=new PdfGState();
				state.setFillOpacity(opacity);
				state.setStrokeOpacity(opacity);
				cb.setGState(state);
			}		
			cb.beginText();
			cb.setColorFill(ovalColor);
			cb.moveText(x, y);
			//cb.moveText(xBar, yBar);
			cb.setFontAndSize(font,fontSize);
			cb.showText(BarChar);//bars.toString());
			cb.endText();
			cb.restoreState();
			
			x+=barWidth;;
			noPixelsSoFar++;
		}
			
		//draw one letter at a time
		for (int i=0;i<text.length();i++) {
			t=Character.toString(text.charAt(i));
			int noPixelsTheLetterIsWide=Math.round((Math.abs(font.getWidthPoint(t,fontSize))/barWidth));
			noPixelsSoFar+=noPixelsTheLetterIsWide;

			//find the background the exact size as the letter
			cb.saveState();
			{
				PdfGState state=new PdfGState();
				state.setFillOpacity(opacity);
				state.setStrokeOpacity(opacity);
				cb.setGState(state);
			}
			cb.beginText();
			cb.setColorFill(ovalColor);
			cb.moveText(x, y);
			cb.setFontAndSize(font,fontSize);
			cb.showText(dummyBackgrounds[noPixelsTheLetterIsWide-4]);
			cb.endText();
			cb.restoreState();
				
			cb.saveState();
			{
				PdfGState state=new PdfGState();
				state.setFillOpacity(1);
				state.setStrokeOpacity(1);
				cb.setGState(state);
			}
			cb.beginText();
			cb.setColorFill(white);
			cb.moveText(x, y);
			cb.setFontAndSize(font,fontSize);
			cb.showText(t);
			cb.endText();
			cb.restoreState();
	
			//draw the confirmation numbers
			cb.saveState();
			{
				PdfGState state=new PdfGState();
				state.setFillOpacity(opacity);
				state.setStrokeOpacity(opacity);
				cb.setGState(state);
			}
			cb.beginText();
			cb.setColorFill(p_symbolColor);
			cb.moveText(x, y);
			cb.setFontAndSize(font,fontSize);
			cb.showText(t);
			cb.endText();
			cb.restoreState();
			
			x+=noPixelsTheLetterIsWide*barWidth;
		}
		
		for (int i=0;i<noTotalPixels-noPixelsSoFar;i++) {
			cb.saveState();
			{
				PdfGState state=new PdfGState();
				state.setFillOpacity(opacity);
				state.setStrokeOpacity(opacity);
				cb.setGState(state);
			}		
			cb.beginText();
			cb.setColorFill(ovalColor);
			cb.moveText(x, y);
			//cb.moveText(xBar, yBar);
			cb.setFontAndSize(font,fontSize);
			cb.showText(BarChar);//bars.toString());
			cb.endText();
			cb.restoreState();
			
			x+=barWidth;;
		}

		//addDecoyLayer(cb, font, fontSize, xBar, yBar, barWidth, noTotalPixels);		
		//addDecoyCodes(cb, font, fontSize, xBar, yBar, barWidth, noTotalPixels);
	}
	
	private static void addDecoyCodes(PdfContentByte cb, BaseFont font, int fontSize, float x, float y, float barWidth,int noTotalPixels) {
		//draw a white background
		int numberofDecoyCodes=5;
		for (int i=0;i<numberofDecoyCodes;i++) {
			String currentCode="";
			while (Math.round((Math.abs(font.getWidthPoint(currentCode,fontSize))/barWidth))<noTotalPixels)
			{
				currentCode+=InvisibleInkCodes.CodesAlphabet[(int)(Math.random()*InvisibleInkCodes.CodesAlphabet.length)];
			}
			currentCode=currentCode.substring(1);
//			System.out.println(currentCode);
			//place the code
			
			//int randomOffset=(int)(Math.random()*Math.max(0,(noTotalPixels*0.4)));
			
			int noPixelsTheTextIsWide=Math.round((Math.abs(font.getWidthPoint(currentCode,fontSize))/barWidth));
			int randomOffset=2+(int)(Math.random()*Math.max(0,((noTotalPixels-noPixelsTheTextIsWide)-4)));
			
			//int randomOffset=(int)(Math.random()*3);
			
			float currentx=x+randomOffset*barWidth;
			
			float currentDecoyOpacity=decoyOpacity+(float)(Math.random()/100*6-0.03);
			for (int j=0;j<currentCode.length();j++) {
				String t=Character.toString(currentCode.charAt(j));
				int noPixelsTheLetterIsWide=Math.round((Math.abs(font.getWidthPoint(t,fontSize))/barWidth));
		
				//draw the decoy codes
				cb.saveState();
				{
					PdfGState state=new PdfGState();
					state.setFillOpacity(currentDecoyOpacity);
					state.setStrokeOpacity(currentDecoyOpacity);
					//state.setBlendMode(PdfGState.BM_LIGHTEN);
					cb.setGState(state);
				}
				cb.beginText();
				cb.setColorFill(decoyCodesColor);
				cb.moveText(currentx, y);
				cb.setFontAndSize(font,fontSize);
				cb.showText(t);
				cb.endText();
				cb.restoreState();
				
				currentx+=noPixelsTheLetterIsWide*barWidth;
			}
			allDecoyCodes+=randomOffset+currentCode+" ";
		}
		allDecoyCodes+="\n";
	}

	private static void addDecoyLayer(PdfContentByte cb, BaseFont font, int fontSize, float x, float y, float barWidth,int noTotalPixels) {
			String currentCode=dummyBackgrounds[0]+dummyBackgrounds[0]+dummyBackgrounds[0]+dummyBackgrounds[0]+dummyBackgrounds[0]+dummyBackgrounds[0]+dummyBackgrounds[0];
			int randomOffset=1;
			
			float currentx=x+randomOffset*barWidth;
			
			float currentDecoyOpacity=0.05f;
			for (int j=0;j<currentCode.length();j++) {
				String t=Character.toString(currentCode.charAt(j));
				int noPixelsTheLetterIsWide=Math.round((Math.abs(font.getWidthPoint(t,fontSize))/barWidth));
		
				//draw the decoy codes
				cb.saveState();
				{
					PdfGState state=new PdfGState();
					state.setFillOpacity(currentDecoyOpacity);
					state.setStrokeOpacity(currentDecoyOpacity);
					//state.setBlendMode(PdfGState.BM_LIGHTEN);
					cb.setGState(state);
				}
				cb.beginText();
				cb.setColorFill(decoyCodesColor);
				cb.moveText(currentx, y);
				cb.setFontAndSize(font,fontSize);
				cb.showText(t);
				cb.endText();
				cb.restoreState();
				
				currentx+=noPixelsTheLetterIsWide*barWidth;
			}
	}

	
/*
	public static void addTextCentered(PdfContentByte cb, Rectangle possition, BaseFont font, int fontSize,Color textColor,String text) {
		//draw a white background
		cb.saveState();
		cb.setColorFill(Color.WHITE);
		cb.setColorStroke(Color.WHITE);
		cb.rectangle(possition.getLeft(), possition.getBottom(), possition.getWidth(), possition.getHeight());
		cb.fillStroke();
		cb.restoreState();
		
		float rectLeft=possition.getLeft();
		float rectBottom=possition.getBottom();
		
		float textWidthPoints=Math.abs(font.getWidthPoint(text,fontSize));
		float textHeigthPoints=Math.abs(font.getAscentPoint(text,fontSize));//+Math.abs(font.getDescentPoint(text,fontSize));


		//check how many | charachters fit in the xoffset
		float barWidth=Math.abs(font.getWidthPoint(BarChar,fontSize));		
		//int noBarsBeforeText=(int)(xoffset / barWidth +0.0f);
		//float xDummyInk=xCode-noBarsBeforeText*barWidth;
		StringBuffer bars=new StringBuffer("");
		for (int i=0;i<=(int)(possition.getWidth()/barWidth);i++)
			bars.append(BarChar);
		
		System.out.println("barWidth="+barWidth+" allBarsWidth="+Math.abs(font.getWidthPoint(bars.toString(),fontSize)));
		
		float xBar=rectLeft;
		float yBar=rectBottom+(possition.getHeight()-textHeigthPoints)/2;
		
		//float xoffset=(possition.getWidth()-textWidthPoints)/2;
		int randomOffset=(1+(int)(Math.random()*2));
		float xCode=xBar+randomOffset*barWidth;
System.out.println("xBar="+xBar+" randomOffset="+randomOffset+" barWidth="+barWidth+" xCode="+xCode);		
		float yCode=yBar;		

System.out.println("xBar="+xBar+" yBar="+yBar+" xCode="+xCode+" yCode="+yCode+" barWidth="+barWidth);		
		
		//draw the DUMMY invizible ink
		cb.saveState();
		{
			PdfGState state=new PdfGState();
			state.setFillOpacity(opacity);
			cb.setGState(state);
		}		
		cb.beginText();
		cb.setColorFill(dummyInvisibleInkColor);
		cb.moveText(xBar, yBar);
		cb.setFontAndSize(font,fontSize);
		cb.showText(bars.toString());
		cb.endText();
		cb.restoreState();		

		//draw WHITE letters to mask the dummy in the back
		cb.saveState();
		{
			PdfGState state=new PdfGState();
			state.setFillOpacity(1);
			cb.setGState(state);
		}
		cb.beginText();
		cb.setColorFill(Color.WHITE);
		cb.moveText(xCode, yCode);
		cb.setFontAndSize(font,fontSize);
		cb.showText(text);
		cb.endText();
		cb.restoreState();

		//draw the confirmation numbers
		cb.saveState();
		{
			PdfGState state=new PdfGState();
			state.setFillOpacity(opacity);
			cb.setGState(state);
		}
		cb.beginText();
		cb.setColorFill(textColor);
		cb.moveText(xCode, yCode);
		cb.setFontAndSize(font,fontSize);
		cb.showText(text);
		cb.endText();
		cb.restoreState();
	}
*/
	private void createBlankBackgroundPage(float w,float h) {
		com.itextpdf.text.Document document = new com.itextpdf.text.Document(new Rectangle(w,h));
		try {
			PdfWriter.getInstance(document,
					new FileOutputStream("__BlankPdf.pdf"));
			/* do this in test ballots
				HeaderFooter header = new HeaderFooter(new Phrase("Test Ballot"), false);
				HeaderFooter footer = new HeaderFooter(new Phrase("This ballot whould not be used in a real election"), new Phrase("."));
				footer.setAlignment(Element.ALIGN_CENTER);
				document.setHeader(header); 
				document.setFooter(footer);
			*/ 			
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

	protected void addSerialNumber(String serial,String prefixForFieldName) {
    	serialFontSize=getFontSize(geom.getSerialTop("0"), helv);//serialFont);
    	
        //step3 - add the serial number in latin
    	Rectangle r=null;
        for (int i=0;i<geom.getNoDigitsInSerial();i++) {
        	r=geom.getSerialTop(i+"");
        	
        	//System.out.println("geom.getNoDigitsInSerial()="+geom.getNoDigitsInSerial());
        	
        	drawWhiteRectangle(r);
        	
        	pdfFormField = makeText(
        			r, 
        			prefixForFieldName+"serialTop_"+i,
            		helv,//serialFont,
            		serialFontSize,
            		Character.toString(serial.charAt(i)));
            writer.addAnnotation(pdfFormField);
        }
        

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
        //char bullet=162;
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
    	            		Character.toString(new Character((char)(116+digit))));
    	            		//Character.toString(bullet));
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
	
    public static void main(String[] args) throws Exception {
    	String publicFolder=InputConstants.publicFolder;
		ElectionSpecification es=new ElectionSpecification(InputConstants.ElectionSpec);
		BallotGeometry geom=new BallotGeometry(InputConstants.Geometry);

		//String background=dir+"policy ballot (RGB) funny sizes.pdf";
		//oclugBallot-Draft08.pdf";
		//String background=dir+"policy ballot background test at 80% (RGB).pdf";
		//String background=dir+"Takoma Park 2007 ballot scantegrity source11.pdf";
		String background=publicFolder+"backgorund.pdf";
		String pathToPrintsFile=InputConstants.MeetingTwoPrints;
		
    	PrintableBallotMaker pbm=new PrintableBallotMaker(es,geom);
    	pbm.init(background,pathToPrintsFile);
    	pbm.makePrintableBallots(InputConstants.privateFolder+"", 5,9);
    	
/*    	
    	int noBallotsToPrint=200;
    	int firstBallot=1000;
    	int batchSize=100;
    	for (int i=firstBallot;i<firstBallot+noBallotsToPrint;i+=batchSize) {
    		pbm.makePrintableBallots(InputConstants.privateFolder+"", i,i+batchSize-1);	
    	}
*/    	
    	    	
    }
}
