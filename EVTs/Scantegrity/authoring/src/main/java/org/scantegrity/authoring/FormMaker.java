package org.scantegrity.authoring;

import java.awt.Color;
import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.xml.sax.SAXException;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.ContestSymbols;
import org.scantegrity.common.Util;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.Document;
import com.itextpdf.text.DocumentException;
import com.itextpdf.text.Paragraph;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.BaseFont;
import com.itextpdf.text.pdf.PdfAction;
import com.itextpdf.text.pdf.PdfAnnotation;
import com.itextpdf.text.pdf.PdfAppearance;
import com.itextpdf.text.pdf.PdfContentByte;
import com.itextpdf.text.pdf.PdfFormField;
import com.itextpdf.text.pdf.PdfGState;
import com.itextpdf.text.pdf.PdfImportedPage;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfWriter;

/**
 * It generates a pdf form as a blank ballot.
 *  
 * The form contains all the javascript logic and is created from the geometry, the Election Spec and a pdf background
 * @author stefan
 *
 */
public class FormMaker {

	protected BaseFont helv = null;
	protected BaseFont serialFont=null;
	
	protected int serialFontSize = 14;
	protected int symbolTopFontSize = 8;
	protected int symbolBottomFontSize = 8;
	
	protected String jsInitValues = "";
	protected String jsFunctions = "";
	
	protected PdfContentByte cb;
	protected PdfWriter writer;
//Amir editing
	//protected static final BaseColor orange = new BaseColor(Color.BLACK);	
	protected static final BaseColor orange = new BaseColor(0,0,0);
	//protected static final BaseColor green = new BaseColor(Color.GREEN);
	protected static final BaseColor green = new BaseColor(0,255,0);
	//protected static final BaseColor white = new BaseColor(Color.WHITE);
	protected static final BaseColor white = new BaseColor(255,255,255);
	//protected static final BaseColor black = new BaseColor(Color.WHITE);
	protected static final BaseColor black = new BaseColor(255,255,255);
	//protected static final BaseColor red = new BaseColor(Color.RED);	
	protected static final BaseColor red = new BaseColor(255,0,0);
	//protected static final BaseColor gray = new BaseColor(Color.GRAY);
	protected static final BaseColor gray = new BaseColor(108,108,108);
	//protected static final BaseColor yellow = new BaseColor(Color.YELLOW);
	protected static final BaseColor yellow = new BaseColor( 255, 255, 0);
	
	protected BallotGeometry geom=null;
	protected Question[] qs=null;

    protected PdfFormField pdfFormField;
    protected Rectangle rect;
    
    protected static String serialFontPath="TENHB192.TTF";

//Amir editing
    //protected BaseColor symbolColor=new BaseColor(Color.BLACK);
      protected BaseColor symbolColor   = new BaseColor(0,0,0);
    
    String[] canonicalSymbols=null;
    
    /**
     * creates the javascript to put in the pdf from the ElectionSpec
     * and from jsFunctions.js . This file must be next to this class (the path is relative)
     * 
     * @param es - the Election Specification
     * @param geom - the geometry of the ballot (coresponding to the Election Spec)
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
     */
	public FormMaker(ElectionSpecification es,BallotGeometry geom) throws Exception, DocumentException {
		this.geom=geom;
		StringBuffer jsiv=new StringBuffer("");
		qs = es.getOrderedQuestions();		
		jsiv.append(
				"var noq="+qs.length+";\n" +
				"var noDigitsInSerial="+geom.getNoDigitsInSerial()+";\n" +
				"var noa = new Array(noq);\n" +
				"var maxAPerQ = new Array(noq);\n" +
				"var qType = new Array(noq);\n" +
				"var vote = new Array(noq);\n" +
				"\n");
		
		//set the variables in the JavaScript code
		for (int i=0;i<qs.length;i++) {
			jsiv.append(
					"noa["+i+"]="+qs[i].getAnswers().size()+";\n" +
					"maxAPerQ["+i+"]="+qs[i].getMax()+";\n");
			if (qs[i].getTypeOfAnswer().compareTo(Constants.ONE_ANSWER)==0)
				jsiv.append("qType["+i+"]=\"one\";\n");
			else
				if (qs[i].getTypeOfAnswer().compareTo(Constants.MULTIPLE_ANSWERS)==0)
					jsiv.append("qType["+i+"]=\"many\";\n");
				else
					if (qs[i].getTypeOfAnswer().compareTo(Constants.RANK)==0)					
						jsiv.append("qType["+i+"]=\"rank\";\n");
		}
		jsiv.append("\n");
		
		jsInitValues = jsiv.toString();
		
		//load the JavaScript Functions
		loadJavaScript();
		
		//System.out.print(Arrays.deepToString(new File(getClass().getResource(".").toURI()).list()));
		
		//helv = BaseFont.createFont("Helvetica", "winansi", BaseFont.EMBEDDED);
		helv = BaseFont.createFont("Courier", BaseFont.CP1252, BaseFont.EMBEDDED);
		//System.out.println(getClass().getResource(serialFontPath).toString());		
		serialFont = BaseFont.createFont(getClass().getResource(serialFontPath).toString(), BaseFont.CP1252, BaseFont.EMBEDDED);
		
		ContestSymbols cs=new ContestSymbols(null,es,ContestSymbols.alphabet,false);
		canonicalSymbols=cs.getCanonicalSymbols();
	}

	protected void loadJavaScript() throws IOException {
		StringBuffer jsf=new StringBuffer("");
		InputStream input = getClass().getResourceAsStream("jsFunctions.js");		
		
        BufferedReader bufRead = new BufferedReader(new InputStreamReader(input));        
        String line = bufRead.readLine();
        jsf.append(line);
        
        do {
        	jsf.append(line);
        	jsf.append("\n");
        	line = bufRead.readLine();        	
        } while (line != null);
        bufRead.close();
        
        jsFunctions = jsf.toString();		
	}
	/**
	 * creates a pdf from representing a ballot, with the only thing missing
	 * being the letters.
	 * 
	 * All the fonts are embeded, the pdf is compressed. Version 1.3 of the pdf is used.
	 * 
	 * To properly view the pdf Adobe Reader or Adobe Acrobat must be used. 
	 * Other viewers will not display it properly (do not imperpret javascript correctly)
	 * 
	 * @param background - the background to be used. If null or there is an error reading the background, a white background is used  
	 * @param outFile - where the form is produced
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public void make(String background, String outFile) throws DocumentException, IOException {		        
        //Start building the document
        
        //step1 - add the background
        PdfReader reader = null;
        if (background==null) {
        	//set a default white background
        	Rectangle paperSize=new Rectangle(geom.getWidth()*72,geom.getHeight()*72);//PageSize.LETTER;
        	Document document = new Document(paperSize,0,0,0,0);
    		try {
    			PdfWriter.getInstance(document,
    					new FileOutputStream("__BlankPdf.pdf"));
    			document.open();
    			document.add(new Paragraph(" "));
    			document.close();
    		} catch (DocumentException de) {
    			System.err.println(de.getMessage());
    		} catch (IOException ioe) {
    			System.err.println(ioe.getMessage());
    		}
    		background="__BlankPdf.pdf";
        }
        
        reader = new PdfReader(background);
		Document.compress = true;

		Document document = new Document(reader.getPageSize(1));

        writer = PdfWriter.getInstance(document, new FileOutputStream(outFile));
        writer.setViewerPreferences(PdfWriter.PageLayoutSinglePage);        
        //writer.setPdfVersion(PdfWriter.VERSION_1_2);        
        writer.setPdfVersion(PdfWriter.VERSION_1_3);
        document.open();
        cb = writer.getDirectContent();
        PdfImportedPage page1 = writer.getImportedPage(reader, 1);
        
        cb.addTemplate(page1,0,0);        	
    	document.setMargins(0,0,0,0);        	
        cb.moveTo(0, 0);
        
        //step2 - add the javascript
        addJavaScript();
//System.out.println(jsInitValues+jsFunctions.toString());        
        addSerialNumber();
        addContests();
        
        //addFinishButtons();
        //addHideSymbolsButtons();
        
        addPrintBothPagesButton();
        //addEmailButton();
        
        addAlignment();
        
        document.close();
	}
	
	protected void addJavaScript() {
		writer.addJavaScript(jsInitValues+jsFunctions.toString());		
	}
	
	protected void addSerialNumber() {
		addSerialNumber(Util.AddleadingZeros("", geom.getNoDigitsInSerial()), "");
	}
	
    protected void addSerialNumber(String serial,String prefixForFieldName) {
		serialFontSize=getFontSize(geom.getSerialTop("0"), serialFont);

        //step3 - add the serial number
		Rectangle r=null;
        for (int i=0;i<geom.getNoDigitsInSerial();i++) {
        	r=geom.getSerialTop(i+"");
        	drawWhiteRectangle(r);
        	pdfFormField = makeText(
        			r, 
            		prefixForFieldName+"serialTop_"+i,
            		serialFont,
            		serialFontSize,
            		Character.toString(serial.charAt(i)));
            writer.addAnnotation(pdfFormField);
            
            r=geom.getSerialBottom(i+"");
            drawWhiteRectangle(r);
        	pdfFormField = makeText(
        			r, 
            		prefixForFieldName+"serialBottom_"+i, 
            		serialFont,
            		serialFontSize,
            		Character.toString(serial.charAt(i)));
            writer.addAnnotation(pdfFormField);
        }        
    }
    
    protected void addContests() {
    	addContests(canonicalSymbols,canonicalSymbols,"");
    }
    
    protected void addContests(String[] allSymbolsTop,String[] allSymbolsBottom,String prefixForFieldName) {
    	symbolTopFontSize=getFontSize(geom.getTop("0","0"),helv);
    	symbolBottomFontSize=symbolTopFontSize;//getFontSize(geom.getBottom("0","0","0"),helv);
    	
        String sufix;
    	
    	String func="";
    	int noRanks=1;
    	int allSymbolsPos=0;
        //step3 - for each race, add the placeholders for symbols
        for (int qno=0;qno<qs.length;qno++) {        	
        	//step 3.1 add the top symbols
        	//for each candidate
        	for (int ano=0;ano<qs[qno].getAnswers().size();ano++) {
        		sufix = "_"+qno+"_"+ano;
        		rect = geom.getTop(qno+"",ano+"");
        		
        		drawWhiteRectangle(rect);
        		
            	pdfFormField = makeText(
            			rect, 
            			prefixForFieldName+"topSymbol"+sufix,
                		helv,
                		symbolTopFontSize,
                		allSymbolsTop[allSymbolsPos]);
                writer.addAnnotation(pdfFormField);
        		                
                pdfFormField = makeButtonHighlightCandidate(
                		rect,
                		prefixForFieldName+"highlightCandidate"+sufix);
                writer.addAnnotation(pdfFormField);

                pdfFormField = makeButtonVoteTop(
            			rect, 
            			prefixForFieldName+"voteTop"+sufix);
            	pdfFormField.setAction(PdfAction.javaScript("voteTop("+qno+","+ano+");", writer));
                writer.addAnnotation(pdfFormField);                	                                        

            	//step 3.2 for each row (rank), add the bottom symbols and the orange (top, bottom and both)
                noRanks=1;
                if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)
                	noRanks=qs[qno].getMax();
                for (int rank=0;rank<noRanks;rank++) {                	
                	sufix = "_"+qno+"_"+rank+"_"+ano;
                	
                	rect = geom.getBottom(qno+"",rank+"",ano+"");
                	                	
                	drawWhiteRectangle(rect);
                	
                	pdfFormField = makeButtonOrangeTop(
                			rect, 
                			prefixForFieldName+"orangeTop"+sufix);
                    writer.addAnnotation(pdfFormField);                	
                    
                	pdfFormField = makeButtonTopHoles(
                			rect, 
                			prefixForFieldName+"topHole"+sufix);
                    writer.addAnnotation(pdfFormField);                	                    
                    
                	pdfFormField = makeButtonOrangeBottom(
                			rect, 
                			prefixForFieldName+"orangeBottom"+sufix);
                    writer.addAnnotation(pdfFormField);                	
                    
                	pdfFormField = makeButtonOrangeBoth(
                			rect, 
                			prefixForFieldName+"orangeBoth"+sufix);
                    writer.addAnnotation(pdfFormField);                    
                    
                	pdfFormField = makeText(
                			rect, 
                			prefixForFieldName+"bottomSymbol"+sufix,
                    		helv,
                    		symbolBottomFontSize,
                    		allSymbolsBottom[allSymbolsPos]);
                    writer.addAnnotation(pdfFormField);
                    
                	pdfFormField = makeButtonVoteBottom(
                			rect, 
                			prefixForFieldName+"voteBottom"+sufix);
        			if (qs[qno].getTypeOfAnswer().compareTo(Constants.ONE_ANSWER)==0)
        				func="voteOne("+qno+","+ano+");";
        			else
        				if (qs[qno].getTypeOfAnswer().compareTo(Constants.MULTIPLE_ANSWERS)==0)
        					func="voteMany("+qno+","+ano+");";
        				else
        					if (qs[qno].getTypeOfAnswer().compareTo(Constants.RANK)==0)					
        						func="voteRank("+qno+","+rank+","+ano+");";
                	pdfFormField.setAction(PdfAction.javaScript(func, writer));
                    writer.addAnnotation(pdfFormField);                	                                        
                }
                allSymbolsPos++;
        	}
        }
    }
    
    protected void addFinishButtons() {
        //step4 - add the Finish voting button
        //one up and one down
        rect = geom.getUpperFinishButton();
    	pdfFormField = makeButtonFinishVoting(
    			rect, 
        		"doneWithSelection0",
        		"Finish Selection");
    	pdfFormField.setAction(PdfAction.javaScript("finishSelection();", writer));
        //writer.addAnnotation(pdfFormField);              	                                        
      
        rect = geom.getLowerFinishButton();
    	pdfFormField = makeButtonFinishVoting(
    			rect, 
        		"doneWithSelection1",
        		"Proceed to Ballot Casting");
    	pdfFormField.setAction(PdfAction.javaScript("finishSelection();", writer));
        writer.addAnnotation(pdfFormField);              	                                                
        
        
        rect = geom.getInstructionButton();
    	pdfFormField = makeButtonInstructions(
    			rect, 
        		"instructions",
        		"Instructions");
    	pdfFormField.setAction(PdfAction.javaScript("welcome();", writer));
        writer.addAnnotation(pdfFormField);              	                                                        
    }

    protected void addPrintBothPagesButton() {
        rect = geom.getLowerFinishButton();
    	pdfFormField = makeButtonFinishVoting(
    			rect, 
        		"doneWithSelection1",
        		"Cast Ballot");
    	if (Math.random()<0.5)
    		pdfFormField.setAction(PdfAction.javaScript("choosePage(\"top\");printLoudly();showAllSymbols();showBothSerials();choosePage(\"bottom\");printSilently();", writer));
    	else
    		pdfFormField.setAction(PdfAction.javaScript("choosePage(\"bottom\");printLoudly();showAllSymbols();showBothSerials();choosePage(\"top\");printSilently();", writer));
        writer.addAnnotation(pdfFormField);              	                                                    	
    }

    protected void addEmailButton() {
        rect = geom.getLowerFinishButton();
    	pdfFormField = makeButtonFinishVoting(
    			rect, 
        		"doneWithSelection1",
        		"Cast Ballot");
    	pdfFormField.setAction(PdfAction.javaScript("finishSelection();sendEmail();", writer));
        writer.addAnnotation(pdfFormField);              	                                                    	
    }
    
    
    protected void addHideSymbolsButtons() {
        rect = geom.getHideTop();
    	pdfFormField = makeButtonShowAll(
    			rect, 
        		"hideTop",
        		"Hide Top");
    	pdfFormField.setAction(PdfAction.javaScript("showAllSymbols();hideSymbols(\"bottom\");", writer));
        writer.addAnnotation(pdfFormField);              	                                        
      
        rect = geom.getHideBottom();
    	pdfFormField = makeButtonShowAll(
    			rect, 
        		"hideBottom",
        		"Hide Bottom");
    	pdfFormField.setAction(PdfAction.javaScript("showAllSymbols();hideSymbols(\"top\");", writer));
        writer.addAnnotation(pdfFormField);              	                                        
        
        rect = geom.getShowBoth();
    	pdfFormField = makeButtonShowAll(
    			rect, 
        		"showBoth",
        		"Show Both");
    	pdfFormField.setAction(PdfAction.javaScript("showAllSymbols();", writer));
        writer.addAnnotation(pdfFormField);              	                                        
    }
    
    public void addAlignment() {
    	addAlignment("0");
    }
    public void addAlignment(String page) {
        //step5 add black alignment marks    	
    	Rectangle rect = geom.makeRectangle(geom.getUpperAlignment());
    	drawWhiteRectangle(rect);
    	drawBlackDiskStatic(cb,rect);
    	/*
    	PdfFormField pdfFormField = makeButtonAlignmentMark(
    			rect, 
        		page+"_ul");
        writer.addAnnotation(pdfFormField);                	
    	 */
        rect = geom.makeRectangle(geom.getLowerAlignment());
        drawWhiteRectangle(rect);
      	drawBlackDiskStatic(cb,rect);
      	/*
    	pdfFormField = makeButtonAlignmentMark(
    			rect, 
        		page+"_lr");
        writer.addAnnotation(pdfFormField);
        */
	}
    
    /** 
     * @param possition - the possition for the created pdf field
     * @param name - the name of the field (used when filling it in)
     * @param font - the font used when filling in the form
     * @param fontSize - the size of the font
     * @return - a PdfFormField of type text, read-only, centered, and printable
     */
	public PdfFormField makeText(Rectangle possition, String name, BaseFont font, int fontSize,String defaultText) {
		
        PdfFormField field = PdfFormField.createTextField(writer, false, false, 0);
        field.setWidget(possition, PdfAnnotation.HIGHLIGHT_INVERT);

        field.setFieldFlags(PdfFormField.FF_READ_ONLY);
        field.setFieldName(name);
        field.setValueAsString(defaultText);
        field.setDefaultValueAsString(defaultText);
        field.setPage();
        field.setQuadding(PdfFormField.Q_CENTER);
        PdfAppearance da = cb.createAppearance(possition.getWidth(), possition.getHeight());
        da.setFontAndSize(font, fontSize);
        da.setColorFill(symbolColor);
        field.setDefaultAppearanceString(da);
        field.setFlags(PdfAnnotation.FLAGS_PRINT);
/*        
        da.beginVariableText();
        da.saveState();
        da.rectangle(2, 2, 167, 15);
        da.clip();
        da.newPath();
        da.beginText();
        da.setFontAndSize(helv, fontSize);
        da.setColorFill(Color.BLACK);
        da.setTextMatrix(4, 5);
        da.showText(defaultText);
        da.endText();
        da.restoreState();
        da.endVariableText();        
*/        
        field.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, da);
        return field;
	}
	
	/**
	 * @param possition - where the pdf field should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button with a black donut on it (as it would appear when a voter choses the top page)
	 * The donut is as big as the given rectangle and the hole as half the diameter
	 */
	public PdfFormField makeButtonOrangeTop(Rectangle possition, String name) {
		possition=new Rectangle(possition.getLeft()-(float)geom.getDonutThicknessTop()*72,
				possition.getBottom()-(float)geom.getDonutThicknessTop()*72,
				possition.getRight()+(float)geom.getDonutThicknessTop()*72,
				possition.getTop()+(float)geom.getDonutThicknessTop()*72);
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l/2);
        normal.fill();
        normal.setColorFill(white);
        normal.circle(w/2,h/2,(float)geom.getHoleDiameter()/2*72);
        normal.fill();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button with a black bullet on it (as it would appear when a voter choses the bottom page)
	 * The bullet is as big as the side of the given rectangle
	 */
	public PdfFormField makeButtonOrangeBottom(Rectangle possition, String name) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        
        PdfGState transparent=new PdfGState();
        transparent.setFillOpacity(0.75f);        
        transparent.setFillOpacity(1);
                
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.saveState();
        normal.setGState(transparent);

        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l*0.5f);
        normal.fill();
        
        normal.setColorFill(white);
        normal.circle(w/2,h/2,l*0.4f);
        normal.fill();
        
        normal.restoreState();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button that gets highlighed when rolled over
	 */
	public PdfFormField makeButtonHighlightCandidate(Rectangle possition, String name) {
		Rectangle localPossition=new Rectangle(possition);
		float rightSpam=0.0f;
		localPossition.setRight(localPossition.getRight()+rightSpam*72);
		float h = localPossition.getHeight();
		float w = localPossition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        
        PdfGState transparent=new PdfGState();
        transparent.setFillOpacity(0.75f);        
        
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.saveState();
        normal.setGState(transparent);
        normal.setColorFill(green);
        normal.rectangle(0,0,w,h);
        normal.fill();
        normal.restoreState();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(localPossition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}	

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button with a black bullet on it (as it would appear when a voter marks)
	 * The button is black and 0.75 transparent.
	 */
	public PdfFormField makeButtonOrangeBoth(Rectangle possition, String name) {
//System.out.println(possition.getLeft()+" "+possition.getBottom()+" "+possition.getRight()+" "+possition.getTop());		
		
		possition=new Rectangle(
				possition.getLeft()-(float)geom.getDonutThicknessTop()*72,
				possition.getBottom()-(float)geom.getDonutThicknessTop()*72,
				possition.getRight()+(float)geom.getDonutThicknessTop()*72,
				possition.getTop()+(float)geom.getDonutThicknessTop()*72);
				
//System.out.println(possition.getLeft()+" "+possition.getBottom()+" "+possition.getRight()+" "+possition.getTop());		
		float h = possition.getHeight();
		float w = possition.getWidth();
//System.out.println(w+" "+h);		
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        
        PdfGState transparent=new PdfGState();
        //transparent.setFillOpacity(0.75f);
        transparent.setFillOpacity(1f);
        
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.saveState();
        normal.setGState(transparent);

/*        
        normal.setColorFill(orange);
        normal.ellipse(0,0,w,h);
        //normal.circle(w/2,h/2,l/2);
        normal.fill();
*/
        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l*0.5f);
        normal.fill();
        
        normal.setColorFill(white);
        normal.circle(w/2,h/2,l*0.4f);
        normal.fill();

        
        
        normal.restoreState();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf form with a dashed circle, to mark where the holes are on the top page 
	 */
	public PdfFormField makeButtonTopHoles(Rectangle possition, String name) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        //float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(orange);
        normal.ellipse(0,0,w,h);
        //normal.circle(w/2,h/2,l/2);
        normal.setLineDash(3,3,0);
        normal.stroke();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button with a black circle on it (used for alignment)
	 */
	public  PdfFormField makeButtonAlignmentMark(Rectangle possition, String name) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(black);
        normal.circle(w/2,h/2,l/2);
        normal.fill();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setFlags(PdfAnnotation.FLAGS_PRINT);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @param text - the text that appears on the button
	 * @return - a pdf button pressed when the voter finished his selection
	 */
	public PdfFormField makeButtonFinishVoting(Rectangle possition, String name,String text) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        PdfAppearance normal = cb.createAppearance(w,h);
        
        
        normal.setColorFill(red);
        normal.rectangle(0,0,w,h);
        normal.fill();
        
        normal.setColorFill(gray);
        
        normal.setFontAndSize(helv, 12);
        normal.moveTo(0,0);
        normal.beginText();
        normal.showTextAligned(PdfContentByte.ALIGN_LEFT, text, 5, 10, 0);
        normal.endText();       
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	public PdfFormField makeButtonInstructions(Rectangle possition, String name,String text) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        PdfAppearance normal = cb.createAppearance(w,h);
        
        
        normal.setColorFill(green);
        normal.rectangle(0,0,w,h);
        normal.fill();
        
        normal.setColorFill(gray);
        
        normal.setFontAndSize(helv, 11);
        normal.moveTo(0,0);
        normal.beginText();
        normal.showTextAligned(PdfContentByte.ALIGN_LEFT, text, 3, 10, 0);
        normal.endText();       
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	public PdfFormField makeButtonShowAll(Rectangle possition, String name,String text) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        PdfAppearance normal = cb.createAppearance(w,h);
        
        
        normal.setColorFill(yellow);
        normal.rectangle(0,0,w,h);
        normal.fill();
        
        normal.setColorFill(green);
        
        normal.setFontAndSize(helv, 12);
        normal.moveTo(0,0);
        normal.beginText();
        normal.showTextAligned(PdfContentByte.ALIGN_LEFT, text, 5, 10, 0);
        normal.endText();       
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}
	
	/** 
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button coresponding to where the candidate name and symbol should be
	 * When pressed, the coresponding letter on the bottom gets selected
	 */
	public PdfFormField makeButtonVoteTop(Rectangle possition, String name) {
		Rectangle localPossition=new Rectangle(possition);
		float rightSpam=2.0f;
		localPossition.setRight(localPossition.getRight()+rightSpam*72);		
		float h = localPossition.getHeight();
		float w = localPossition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        PdfAppearance normal = cb.createAppearance(w,h);
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        
        PdfGState transparent=new PdfGState();
        transparent.setFillOpacity(0.5f);
                
        //add flyover
        PdfAppearance rollover = cb.createAppearance(w,h);
        rollover.saveState();
        rollover.setGState(transparent);
        rollover.setColorFill(green);
        rollover.rectangle(0,0,w,h);
        rollover.fill();
        rollover.restoreState();
        
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_ROLLOVER, rollover);
        pushbutton.setWidget(localPossition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	/**
	 * @param possition - where the pdf filed should be placed
	 * @param name - the name of the pdf field
	 * @return - a pdf button coresponding to where the letter on the bottom page is
	 * When pressed, the a black circle covers the letter on the bottom page
	 */
	public PdfFormField makeButtonVoteBottom(Rectangle possition, String name) {
		float h = possition.getHeight();
		float w = possition.getWidth();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        PdfAppearance normal = cb.createAppearance(w,h);
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}
	

	/**
	 * @return the js code from jsFunctions.js (same for all elections)
	 */
	public String getJsFunctions() {
		return jsFunctions;
	}

	/**
	 * @return the js code particular to an election (from the Election Spec)
	 */
	public String getJsInitValues() {
		return jsInitValues;
	}

	/**
	 * @return - the ordered questions from the Election Spec
	 */
	public Question[] getQs() {
		return qs;
	}

	public void drawWhiteRectangle(Rectangle r) {
		drawWhiteRectangleStatic(cb, r);
	}

	public static void drawWhiteRectangleStatic(PdfContentByte cb,Rectangle r) {
		cb.saveState();
		cb.setColorFill(white);
		cb.setColorStroke(white);
		
		//cb.setColorFill(Color.RED);
		//cb.setColorStroke(Color.RED);

		float wider=0.05f;
		cb.rectangle(r.getLeft()-r.getWidth()*wider,r.getBottom()-r.getHeight()*wider,r.getWidth()*(1+2*wider),r.getHeight()*(1+2*wider));
		cb.fillStroke();
		cb.restoreState();
	}

	public static void drawBlackDiskStatic(PdfContentByte cb,Rectangle r) {
		cb.saveState();
		cb.setCMYKColorFillF(0,0,0,1);;
		cb.setCMYKColorStrokeF(0,0,0,1);;
	
		float h = r.getHeight();
		float w = r.getWidth();
        float l=w>h?h:w;
        cb.circle(r.getLeft()+l/2,r.getBottom()+l/2,l/2);
        cb.fillStroke();

		cb.restoreState();
	}
	
	
	/**
	 * @return getFontSize(rect, "R", font)
	 */
    public static int getFontSize(Rectangle rect, BaseFont font) {
    	return getFontSize(rect, "R", font);
    }


    /**
     * increases the size from 0 to until the string does not fit in the rectangle
     * It returns three quarters from this maximum size.
     * @param rect - the bounding rectangle
     * @param zero - the caracter that has to fit in the rectangle
     * @param font - the font the character is in
     * @return - a int representing the three quarters of the size the string has to be in such that 
     * when writen in font "font" it fits in the bounding rectangle
     */
    public static int getFontSize(Rectangle rect, String zero,BaseFont font) {
    	return getFontSize(Math.abs(rect.getWidth()),Math.abs(rect.getHeight()),zero,font);
    }
    
    /**
     * increases the size from 0 to until the string does not fit in a rectangle (width,heigth).
     * It returns three quarters from this maximum size.
     * @param w - the width of thebounding rectangle
     * @param h - the heigth of the bounding rectangle
     * @param zero - the caracter that has to fit in the rectangle
     * @param font - the font the character is in
     * @return - a int representing the three quarters of the size the string has to be in such that 
     * when writen in font "font" it fits in the bounding rectangle
     */
    public static int getFontSize(float w, float h,String zero,BaseFont font) {
    	int size=0;
    	
    	//while the width and the height are noth smaller the the width and the height
    	//of the character, increase the size;
    	
    	float wc=0,hc=0;
    	
    	do {
    		wc=Math.abs(font.getWidthPoint(zero,size));
    		hc=Math.abs(font.getAscentPoint(zero,size))+Math.abs(font.getDescentPoint(zero,size));
    		size++;
    	} while (wc<=w && hc<=h);
    	size--;
//System.out.println("Detected Size "+size);    	
    	int returnedSize=(int)(size*0.85);
//System.out.println("Adjusted Size "+returnedSize);    	
    	return returnedSize;
    }
    
    
    /**
     * debug method
     * @param args
     * @throws ESException
     * @throws SAXException
     * @throws IOException
     * @throws DocumentException
     */
	public static void main(String args[]) throws Exception {
		String dir="Elections/Crypto08/CPSR_Style/";
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");
		BallotGeometry geom = new BallotGeometry(dir+"geometry.xml");
		FormMaker fm = new FormMaker(es,geom);
		String background=dir+"7And1.pdf";
		String outFile=dir+"javaCreatedForm.pdf";
		fm.make(background, outFile);
	}
}
