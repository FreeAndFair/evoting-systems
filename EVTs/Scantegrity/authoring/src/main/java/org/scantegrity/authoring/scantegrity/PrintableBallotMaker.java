// edited by Carsten 

package org.scantegrity.authoring.scantegrity;

// import java.awt.Color;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;

import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.scantegrity.ContestSymbols;

import org.scantegrity.common.BallotGeometry;
import org.scantegrity.common.InputConstants;

import org.scantegrity.common.Util;

import com.itextpdf.text.BaseColor;
import com.itextpdf.text.Document;
import com.itextpdf.text.DocumentException;
import com.itextpdf.text.Paragraph;
import com.itextpdf.text.Rectangle;
import com.itextpdf.text.pdf.BaseFont;
import com.itextpdf.text.pdf.PdfAnnotation;
import com.itextpdf.text.pdf.PdfAppearance;
import com.itextpdf.text.pdf.PdfBorderDictionary;
import com.itextpdf.text.pdf.PdfFormField;
import com.itextpdf.text.pdf.PdfImportedPage;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfWriter;

public class PrintableBallotMaker extends FormMaker 
{
	
	private PdfReader backgroundReader = null;
	ElectionSpecification es=null;
	ContestSymbols cs=null;
	
	public PrintableBallotMaker(ElectionSpecification es,BallotGeometry geom) throws Exception {
		super(es,geom);
		this.es=es;
		symbolColor=new BaseColor(127,127,255);//Color.BLUE;
	}

	protected void addJavaScript() {
		//do not add any javascript
	}
	
	public void init(String background,String[] chars,boolean charReset,String pathToPrintsFile) throws Exception {
		try {
			backgroundReader = new PdfReader(background);
		} catch (Exception e) {
			createBlankBackgroundPage(geom.getWidth()*72,geom.getHeight()*72);
		}
		cs=new ContestSymbols(pathToPrintsFile,es,chars,charReset);		
	}
	
	public void makePrintableBallots(String outputDir,int start,int stop) throws Exception {

		Rectangle pdfPageSize = backgroundReader.getPageSize(1);
		//double scalling = pdfPageSize.getWidth() / ballotMap.getW();
		
		Document document = new Document(pdfPageSize);
		
		File f= new File(outputDir+"/"+start+"-"+stop+".pdf");
		writer = PdfWriter.getInstance(document,new FileOutputStream(f));
		writer.setPdfVersion(PdfWriter.VERSION_1_5);
		writer.setViewerPreferences(PdfWriter.PageModeUseOC);

		document.open();
        cb = writer.getDirectContent();
                
		PdfImportedPage page1 = writer.getImportedPage(backgroundReader, 1);
		document.setMargins(0,0,0,0);
		cb.addTemplate(page1,0,0);
		
		for (int i=start;i<=stop;i++) {
			String serial=cs.getSerialNumber(i);
			String[] allSymbols=cs.getAllSymbols(i,0);
			addAlignment(i+"");
			addSerialNumber(Util.AddleadingZeros(serial,geom.getNoDigitsInSerial()),i+"");
			addContests(allSymbols,allSymbols,i+"");
			
			if (i!=stop) {
				document.newPage();
				cb.addTemplate(page1,0,0);
			}
		}
		
		document.close();		
	}
	protected void addContests(String[] allSymbolsTop,String[] allSymbolsBottom,String prefixForFieldName) {
    	symbolTopFontSize=getFontSize(geom.getTop("0","0","0"),helv);
    	
        String sufix;
    	
    	int allSymbolsPos=0;
        //step3 - for each race, add the placeholders for symbols
        for (int qno=0;qno<qs.length;qno++) {        	
        	//step 3.1 add the top symbols
        	//for each candidate
        	for (int c=0;c<qs[qno].getAnswers().size();c++) {
        		sufix = "_"+qno+"_"+c;                
            	//step 3.2 for each row (rank), add the bottom symbols and the orange (top, bottom and both)
                //for (int rank=0;rank<noRanks;rank++) 
                int rank=0;
                {
                	sufix = "_"+qno+"_"+rank+"_"+c;
                	rect = geom.getTop(qno+"",rank+"",c+"");

                	drawWhiteRectangle(rect);
                	/*
                	pdfFormField = makeButtonTopHoles(
                			rect, 
                			prefixForFieldName+"topHole"+sufix);
                    writer.addAnnotation(pdfFormField);                	
                	*/
                    //put the symbols to the left of the oval. if you put them
                    //in the oval, and the symbol has lots of black, it may get
                    //detected as marked. Plus the voters sees the letter after marking
                	pdfFormField = makeText(
                			translate(rect, 0-rect.getWidth(),0), 
                    		prefixForFieldName+"bottomSymbol"+sufix,
                    		helv,
                    		symbolTopFontSize,
                    		allSymbolsTop[allSymbolsPos]);
                    writer.addAnnotation(pdfFormField);
                }
                allSymbolsPos++;
        	}
        }
    }
	
/*	
	public void drawWhiteRectangle(Rectangle r) {
	}
*/
	
	public PdfFormField makeText(Rectangle possition, String name, BaseFont font, int fontSize,String text) {
		float h = possition.getHeight();
		float w = possition.getWidth();

        cb.moveTo(0, 0);
        PdfFormField field = PdfFormField.createTextField(writer, false, false, 0);
        field.setWidget(possition, PdfAnnotation.HIGHLIGHT_INVERT);
        field.setFlags(PdfAnnotation.FLAGS_PRINT);
        field.setFieldFlags(PdfFormField.FF_READ_ONLY);
        field.setQuadding(PdfFormField.Q_CENTER);
        field.setFieldName(name);
        field.setValueAsString(text);
        field.setDefaultValueAsString(text);
        field.setBorderStyle(new PdfBorderDictionary(2, PdfBorderDictionary.STYLE_SOLID));
        field.setPage();
        
        PdfAppearance tp = cb.createAppearance(w,h);
        PdfAppearance da = (PdfAppearance)tp.getDuplicate();
        da.setFontAndSize(font, fontSize);
        da.setColorFill(BaseColor.BLACK);
        field.setDefaultAppearanceString(da);
        tp.beginVariableText();
        tp.saveState();
        tp.rectangle(0, 0, w,h);
        tp.clip();
        tp.newPath();
        tp.beginText();
        tp.setFontAndSize(font, fontSize);
        tp.setColorFill(BaseColor.BLACK);
        tp.setTextMatrix(0,0);
        tp.showText(text);
        tp.endText();
        tp.restoreState();
        tp.endVariableText();
        field.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, tp);
        return field;
	}

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

    
    public static void main(String[] args) throws Exception {
		String dir=InputConstants.publicFolder;
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");
		BallotGeometry geom=new BallotGeometry(dir+"geometry.xml");

		String background=dir+"dagstuhl background.pdf";
		String pathToPrintsFile=dir+"private/Prints.xml";
		//Vector<Point> range=new Vector<Point>();
		//range.add(new Point(0,9));
    	
    	PrintableBallotMaker pbm=new PrintableBallotMaker(es,geom);
    	pbm.init(background, ContestSymbols.alphabet, true, pathToPrintsFile);
    	pbm.makePrintableBallots(dir, 0,4);
    	
    	
    	
/*    	
		dir="Elections/POLK COUNTY, FLORIDA NOVEMBER 7, 2000/version4Letter/bottom/";
		es=new ElectionSpecification(dir+"ElectionSpec.xml");
		geom=new BallotGeometry(dir+"geometry.xml");

		background=dir+"polk county back sheet watermark2.pdf";
		pathToPrintsFile=dir+"MeetingTwoPrints.xml";
		//Vector<Point> range=new Vector<Point>();
		//range.add(new Point(0,9));
    	
    	pbm=new PrintableBallotMaker(es,geom);
    	pbm.init(background, Util.alphabet.toCharArray(), false, pathToPrintsFile);
    	pbm.makePrintableBallots(dir, 0,99);
*/
    }
}
