package software.authoring.scantegrity;

import java.awt.Color;
import java.io.BufferedReader;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;

import javax.xml.parsers.ParserConfigurationException;

import org.gwu.voting.standardFormat.Constants;
import org.gwu.voting.standardFormat.basic.Question;
import org.gwu.voting.standardFormat.electionSpecification.ElectionSpecification;
import org.gwu.voting.standardFormat.electionSpecification.exceptions.ESException;
import org.xml.sax.SAXException;

import software.authoring.BallotGeometry;

import com.itextpdf.text.Document;
import com.itextpdf.text.DocumentException;
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

public class FormMaker {

	BaseFont helv = null;
	BaseFont serialFont=null;
	private int serialFontSize = 14;
	private int symbolFontSize = 8;
	
	String jsInitValues = "";
	String jsFunctions = "";
	
	private PdfContentByte cb;
	private PdfWriter writer;
	
	Color orange=Color.BLACK;
	
	BallotGeometry geom=null;
	Question[] qs=null;
	
	public FormMaker(ElectionSpecification es,BallotGeometry geom) throws IOException {
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
		StringBuffer jsf=new StringBuffer("");
		FileReader input = new FileReader("src/software/authoring/scantegrity/jsFunctions.js");
        BufferedReader bufRead = new BufferedReader(input);
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

	public void make(String background, String outFile) throws DocumentException, IOException {
		helv = BaseFont.createFont("Helvetica", "winansi", false);		
		serialFont = BaseFont.createFont(getClass().getResource("../TENHB192.TTF").toString(), BaseFont.CP1252, BaseFont.EMBEDDED);
		        
        //Start building the document
        
        //step1 - add the background
        PdfReader reader = null;
        if (background!=null)
        	reader = new PdfReader(background);
        else {
        	
        }
        
		Document.compress = true;
		Document document = new Document(reader.getPageSize(1));

        writer = PdfWriter.getInstance(document, new FileOutputStream(outFile));
        //writer.setPdfVersion(PdfWriter.VERSION_1_2);        
        writer.setPdfVersion(PdfWriter.VERSION_1_4);
        document.open();
        cb = writer.getDirectContent();
        PdfImportedPage page1 = writer.getImportedPage(reader, 1);
        
        cb.addTemplate(page1,0,0);        	
    	document.setMargins(0,0,0,0);        	
        cb.moveTo(0, 0);
        
        //step2 - add the javascript
        writer.addJavaScript(jsInitValues+jsFunctions.toString());
                
        //start adding the fields
        PdfFormField pdfFormField;
        Rectangle rect;
        String sufix;
        //step3 - add the serial number
        for (int i=0;i<geom.getNoDigitsInSerial();i++) {
        	pdfFormField = makeText(
        			geom.getSerialBottom(i+""), 
            		"serialBottom_"+i, 
            		serialFont,
            		serialFontSize);
            writer.addAnnotation(pdfFormField);
        }
    	String func="";
        //step3 - for each race, add the placeholders for symbols
        for (int r=0;r<qs.length;r++) {        	
        	//step 3.1 add the top symbols
        	//for each candidate
        	for (int c=0;c<qs[r].getAnswers().size();c++) {
        		sufix = "_"+r+"_"+c;                
            	//step 3.2 for each row (rank), add the bottom symbols and the orange (top, bottom and both)
                for (int rank=0;rank<geom.getNoRanks(r+"");rank++) {
                	sufix = "_"+r+"_"+rank+"_"+c;
                	rect = geom.getBottom(r+"",rank+"",c+"");

                	pdfFormField = makeButtonTopHoles(
                			rect, 
                    		"topHole"+sufix);
                    writer.addAnnotation(pdfFormField);                	                    
                                        
                	pdfFormField = makeButtonOrangeBoth(
                			rect, 
                    		"orangeBoth"+sufix);
                    writer.addAnnotation(pdfFormField);                    
                    
                	pdfFormField = makeText(
                			rect, 
                    		"bottomSymbol"+sufix,
                    		helv,
                    		symbolFontSize);
                    writer.addAnnotation(pdfFormField);
                    
                	pdfFormField = makeButtonVote(
                			rect, 
                    		"voteBottom"+sufix);
        			if (qs[r].getTypeOfAnswer().compareTo(Constants.ONE_ANSWER)==0)
        				func="voteOne("+r+","+c+");";
        			else
        				if (qs[r].getTypeOfAnswer().compareTo(Constants.MULTIPLE_ANSWERS)==0)
        					func="voteMany("+r+","+c+");";
        				else
        					if (qs[r].getTypeOfAnswer().compareTo(Constants.RANK)==0)					
        						func="voteRank("+r+","+rank+","+c+");";
                	pdfFormField.setAction(PdfAction.javaScript(func, writer));
                    writer.addAnnotation(pdfFormField);                	                                        
                }
        	}
        }
        
        //step4 - add the Finish voting button
        //one up and one down
        rect = geom.getUpperFinishButton();
    	pdfFormField = makeButtonVote(
    			rect, 
        		"doneWithSelection0",
        		"Finish Selection");
    	pdfFormField.setAction(PdfAction.javaScript("finishSelection();", writer));
        writer.addAnnotation(pdfFormField);              	                                        
      
        rect = geom.getLowerFinishButton();
    	pdfFormField = makeButtonVote(
    			rect, 
        		"doneWithSelection1",
        		"Finish Selection");
    	pdfFormField.setAction(PdfAction.javaScript("finishSelection();", writer));
        writer.addAnnotation(pdfFormField);              	                                                
        
        //step5 add black alignment marks
    	rect = geom.getAlignment(0);
    	pdfFormField = makeButtonAlignmentMark(
    			rect, 
        		"ul");
        writer.addAnnotation(pdfFormField);                	

    	rect = geom.getAlignment(1);
    	pdfFormField = makeButtonAlignmentMark(
    			rect, 
        		"lr");
        writer.addAnnotation(pdfFormField);                	
        
        document.close();
	}
	
	public PdfFormField makeText(Rectangle possition, String name, BaseFont font, int fontSize) {
		String defaultText="X";
		
        PdfFormField field = PdfFormField.createTextField(writer, false, false, 0);
        field.setWidget(possition, PdfAnnotation.HIGHLIGHT_INVERT);

        field.setFieldFlags(PdfFormField.FF_READ_ONLY);
        field.setFieldName(name);
        field.setValueAsString(defaultText);
        field.setDefaultValueAsString(defaultText);
        field.setPage();
        field.setQuadding(PdfFormField.Q_CENTER);
        PdfAppearance da = cb.createAppearance(possition.width(), possition.height());
        da.setFontAndSize(font, fontSize);
        da.setColorFill(Color.BLACK);
        field.setDefaultAppearanceString(da);
        field.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, da);
        return field;
	}
	
	public PdfFormField makeButtonOrangeTop(Rectangle possition, String name) {
		float h = possition.height();
		float w = possition.width();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l/2);
        normal.fill();
        normal.setColorFill(Color.WHITE);
        normal.circle(w/2,h/2,l*(float)0.25);
        normal.fill();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}
	
	public PdfFormField makeButtonOrangeBottom(Rectangle possition, String name) {
		float h = possition.height();
		float w = possition.width();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l*(float)0.25);
        normal.fill();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	public PdfFormField makeButtonOrangeBoth(Rectangle possition, String name) {
		float h = possition.height();
		float w = possition.width();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);

        normal.saveState();
        PdfGState gs1 = new PdfGState();
        gs1.setFillOpacity(0.75f);
        normal.setGState(gs1);
        
        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l/2);
        normal.fill();
        
        normal.restoreState();
        
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}

	public PdfFormField makeButtonTopHoles(Rectangle possition, String name) {
		float h = possition.height();
		float w = possition.width();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(orange);
        normal.circle(w/2,h/2,l/2);
        normal.setLineDash(3,3,0);
        normal.stroke();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}
	
	public PdfFormField makeButtonAlignmentMark(Rectangle possition, String name) {
		float h = possition.height();
		float w = possition.width();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        cb.moveTo(0, 0);
        float l=w>h?h:w;
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(Color.BLACK);
        normal.circle(w/2,h/2,l/2);
        normal.fill();
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setFlags(PdfAnnotation.FLAGS_PRINT);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}	

	public PdfFormField makeButtonVote(Rectangle possition, String name) {
		return makeButtonVote(possition,name,"");
	}

	public PdfFormField makeButtonVote(Rectangle possition, String name,String text) {
		float h = possition.height();
		float w = possition.width();
        PdfFormField pushbutton = PdfFormField.createPushButton(writer);
        PdfAppearance normal = cb.createAppearance(w,h);
        normal.setColorFill(Color.GREEN);
        normal.setFontAndSize(helv, 14);
        normal.moveTo(0,0);
        normal.beginText();
        normal.showTextAligned(PdfContentByte.ALIGN_LEFT, text, 10, 10, 0);
        normal.endText();       
        pushbutton.setFieldName(name);
        pushbutton.setAppearance(PdfAnnotation.APPEARANCE_NORMAL, normal);
        pushbutton.setWidget(possition, PdfAnnotation.HIGHLIGHT_PUSH);
        return pushbutton;
	}
	
	public String getJsFunctions() {
		return jsFunctions;
	}

	public String getJsInitValues() {
		return jsInitValues;
	}
	
	public Question[] getQs() {
		return qs;
	}

	public static void main(String args[]) throws ESException, ParserConfigurationException, SAXException, IOException, DocumentException {
		String dir="Elections/cfp/";
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");
		BallotGeometry geom = new BallotGeometry(dir+"geometry.xml");
		FormMaker fm = new FormMaker(es,geom);
		String background=dir+"CFP survey2.5 background.pdf";
		String outFile=dir+"javaCreatedForm.pdf";
		fm.make(background, outFile);
	}
}
