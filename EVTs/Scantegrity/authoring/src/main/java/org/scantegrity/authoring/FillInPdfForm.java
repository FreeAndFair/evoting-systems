package org.scantegrity.authoring;

import java.awt.Point;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Vector;
import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;

import org.scantegrity.common.ContestSymbols;
import org.scantegrity.common.Util;

import com.itextpdf.text.DocumentException;
import com.itextpdf.text.pdf.AcroFields;
import com.itextpdf.text.pdf.PdfFormField;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfStamper;

public class FillInPdfForm {

	/**
	 * 
	 * @param es - the Election Specification
	 * @param form - a blank pdf form (coresponding to the ElectionSpec)
	 * @param pathToPrintsFile - where the prints file from m2 are
	 * @param range - A pdf file is produced for each number in each range. One range is from x(inclusive) to y(inclusive)
	 * @param chars - the chars to be used for filling in the form 
	 * @param charReset - true if for each contest, the chars are taken from the begining of the chars array
	 * @param outDir - the directory where the pdf ballots are written. The names are serial.pdf (where serial is a number)
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static void fillIn(ElectionSpecification es,String form,String pathToPrintsFile,Vector<Point> range,String[] chars, boolean charReset,String outDir) throws Exception {
		ContestSymbols cs=new ContestSymbols(pathToPrintsFile,es,chars,charReset);
		for (int i=0;i<range.size();i++) {
			for (int j=range.get(i).x;j<=range.get(i).y;j++) {
				fillIn(es,form,cs.getSerialNumber(j),cs.getAllSymbols(j, 1),cs.getAllSymbols(j, 0),outDir+cs.getSerialNumber(j)+".pdf");
			}
		}
	}
	
	static void fillIn(ElectionSpecification es,String form,String serial, String[] allTopSymbols,String[] allBottomSymbols,String output) throws FileNotFoundException, DocumentException, IOException {
		PdfReader reader = new PdfReader(form);
		
		PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(output));
        AcroFields form1 = stamp1.getAcroFields();
        
        int ii=0;
        while (form1.getField("serialTop_"+ii)!=null) {
        	ii++;
        }
        
        serial=Util.AddleadingZeros(serial, ii);
        for (int i=0;i<serial.length();i++) {
        	form1.setField("serialTop_"+i,serial.charAt(i)+"");
        	form1.setField("serialBottom_"+i,serial.charAt(i)+"");
        }
        
        Question[] qs=es.getOrderedQuestions();
        int rows=1;
        int count=0;
        for (int i=0;i<qs.length;i++) {
        	for (int j=0;j<qs[i].getAnswers().size();j++) {
        		form1.setField("topSymbol_"+i+"_"+j,allTopSymbols[count]);
        		rows=1;
        		if (qs[i].getTypeOfAnswer().compareTo(Constants.RANK)==0) {
        			rows=qs[i].getMax();
        		}
        		for (int k=0;k<rows;k++) {
        			form1.setField("bottomSymbol_"+i+"_"+k+"_"+j,allBottomSymbols[count]);        			
        			form1.setFieldProperty("bottomSymbol_"+i+"_"+k+"_"+j,"setfflags",PdfFormField.Q_CENTER, null);
        		}
        		count++;
        	}
        }        
        stamp1.close();
	}
	
	/**
	 * TODO this can be made more efficient
	 * 
	 * Given a pdf ballot, it randomly votes it and writes it in a file with the same name, but with sufix Voted
	 * @param fm - used for getting all the Questions and the javascript.
	 * @param FolderWithVirtualBallots - a pdf ballot, or a directory. if it is a directory, it takes all the files from it recursevly and votes them all
	 * @throws Exception - no Exception is caugth and no Exception is Explicitly thrown
	 */
	public static void randomVote(FormMaker fm,String FolderWithVirtualBallots) throws Exception {
		String javaScriptFromForm=fm.getJsInitValues()+fm.getJsFunctions();
		String welcomeAlert="app.alert(\"To ensure your privacy, only half of the letters appearing on this ballot will be returned. There are two groups of letters appearing both to the left and to the right of the choices. It does not affect your vote which group you keep.\");";
		int firstIndexOfWelcomeAlert=javaScriptFromForm.indexOf(welcomeAlert);		
		javaScriptFromForm=javaScriptFromForm.substring(0,firstIndexOfWelcomeAlert)+javaScriptFromForm.substring(firstIndexOfWelcomeAlert+welcomeAlert.length());
		
		String printDialog="this.print({bUI: true,bSilent: true,bShrinkToFit: true});";
		int firstIndexOfPrintDialog=javaScriptFromForm.indexOf(printDialog);
		javaScriptFromForm=javaScriptFromForm.substring(0,firstIndexOfPrintDialog)+javaScriptFromForm.substring(firstIndexOfPrintDialog+printDialog.length());
		
		File f=new File(FolderWithVirtualBallots);
		if (f.isFile()) {		
			PdfReader reader = new PdfReader(FolderWithVirtualBallots);
			String output=FolderWithVirtualBallots.substring(0,FolderWithVirtualBallots.lastIndexOf(Util.fileSeparator)+1)+"Voted"+FolderWithVirtualBallots.substring(FolderWithVirtualBallots.lastIndexOf(Util.fileSeparator)+1);
			PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(output));
			StringBuffer sb=new StringBuffer("");
			
			Question[] qs=fm.getQs();
			int a;
			for (int q=0;q<qs.length;q++) {
				for (int j=0;j<qs[q].getMax();j++) {
					if (Math.random()<0.9) {
						a =(int)(Math.random()*qs[q].getAnswers().size());						
						sb.append("voteTop("+q+","+a+");");
					}
				}
			}
			
		    if (Math.random()<0.5) {
		        sb.append("choosePage(\"top\")");
		    } else {
		    	sb.append("choosePage(\"bottom\")");
		    }
			
			stamp1.addJavaScript(javaScriptFromForm+sb.toString());
			stamp1.close();
		} else {
			File[] allFIles=f.listFiles();
			for (int i=0;i<allFIles.length;i++) {
				randomVote(fm, allFIles[i].getAbsolutePath());
			}
		}
	}

	public static void topAndBottomSeparatly(FormMaker fm,String form) throws Exception {
		String javaScriptFromForm=fm.getJsInitValues()+fm.getJsFunctions();

		String welcomeAlert="app.alert(\"To ensure your privacy, only half of the letters appearing on this ballot will be returned. There are two groups of letters appearing both to the left and to the right of the choices. It does not affect your vote which group you keep.\");";
		int firstIndexOfWelcomeAlert=javaScriptFromForm.indexOf(welcomeAlert);		
		javaScriptFromForm=javaScriptFromForm.substring(0,firstIndexOfWelcomeAlert)+javaScriptFromForm.substring(firstIndexOfWelcomeAlert+welcomeAlert.length());
		
		String printDialog="this.print({bUI: true,bSilent: true,bShrinkToFit: true});";
		int firstIndexOfPrintDialog=javaScriptFromForm.indexOf(printDialog);
		javaScriptFromForm=javaScriptFromForm.substring(0,firstIndexOfPrintDialog)+javaScriptFromForm.substring(firstIndexOfPrintDialog+printDialog.length());
		
		String drawTopHoles="if (page==\"top\") getField(\"topHole_\"+q+\"_\"+r+\"_\"+a).display=display.visible;";
		int firstIndexOfTopHoles=javaScriptFromForm.indexOf(drawTopHoles);
		javaScriptFromForm=javaScriptFromForm.substring(0,firstIndexOfTopHoles)+javaScriptFromForm.substring(firstIndexOfTopHoles+drawTopHoles.length());
		
		topAndBottomSeparatly(fm, form, javaScriptFromForm);
	}
	
	private static void topAndBottomSeparatly(FormMaker fm,String form,String javaScriptFromForm) throws Exception {
		File f=new File(form);
		String[] layers={"top","bottom"};
		if (f.isFile()) {
						
			for (int i=0;i<layers.length;i++) {			
				PdfReader reader = new PdfReader(form);
				
				String output=f.getAbsolutePath();				
				
				output=output.substring(0,output.lastIndexOf(Util.fileSeparator)+1)+layers[i]+"_"+output.substring(output.lastIndexOf(Util.fileSeparator)+1);
				PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(output));
				StringBuffer sb=new StringBuffer("");
				
		        sb.append("choosePage(\""+layers[i]+"\")");
				stamp1.addJavaScript(javaScriptFromForm+sb.toString());
				stamp1.close();
			}
		} else {
			File[] allFIles=f.listFiles();
			for (int i=0;i<allFIles.length;i++) {
				topAndBottomSeparatly(fm, allFIles[i].getAbsolutePath(),javaScriptFromForm);
			}
		}
	}	
	
	/**
	 * debug method 
	 * @param args ElectionSpec PdfForm PrintsFile From0-To0;From1-To1 OutDir Chars
	 * @throws ESException
	 * @throws IOException
	 * @throws DocumentException
	 */
	public static void main(String[] args) throws Exception {
/*		
		ElectionSpecification es=new ElectionSpecification(args[0]);
		Vector<Point> range=new Vector<Point>();;
		StringTokenizer st=new StringTokenizer(args[3],";");
		while (st.hasMoreTokens()) {
			String s=st.nextToken();
			if (s.indexOf('-')==-1)
				range.add(new Point(Integer.parseInt(s),Integer.parseInt(s)));				
			else
				range.add(new Point(Integer.parseInt(s.substring(0,s.indexOf('-'))),Integer.parseInt(s.substring(s.indexOf('-')+1))));
		}
		FillInPdfForm.fillIn(es,args[1],args[2], range, args[4], args[5].toCharArray(), false);
*/
		String dir="Elections/Crypto08/CPSR_Style/";
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");		
		Vector<Point> range=new Vector<Point>();
		range.add(new Point(1048,1048));
/*
		range.add(new Point(5261,5261));
		range.add(new Point(37,37));
		range.add(new Point(2087,2087));
		range.add(new Point(2098,2098));
		range.add(new Point(763,763));
		range.add(new Point(8891,8891));
		range.add(new Point(3901,3901));
		range.add(new Point(9871,9871));
		range.add(new Point(1113,1113));
*/		
		FillInPdfForm.fillIn(es, dir+"javaCreatedForm.pdf",dir+"MeetingTwoPrints.xml",range,ContestSymbols.alphabet,false,dir);
		
		//BallotGeometry geom=new BallotGeometry(dir+"PunchScan/geometry.xml");
		//FillInPdfForm.topAndBottomSeparatly(new FormMaker(es,geom), dir+"PunchScan/pdfBallots/");
		//FillInPdfForm.randomVote(new FormMaker(es,geom), dir+"PunchScan/pdfBallots/");
	}
}