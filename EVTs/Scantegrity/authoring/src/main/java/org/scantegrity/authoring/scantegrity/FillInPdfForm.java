package org.scantegrity.authoring.scantegrity;

import java.awt.Point;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.scantegrity.common.ballotstandards.electionSpecification.exceptions.ESException;
import org.scantegrity.common.scantegrity.ContestSymbols;

import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Util;
import org.scantegrity.common.ScannedBallot;

import com.itextpdf.text.DocumentException;
import com.itextpdf.text.pdf.AcroFields;
import com.itextpdf.text.pdf.PdfFormField;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfStamper;

public class FillInPdfForm {

	/**
	 * @param range
	 * @param outDir
	 * @param chars
	 * @param charReset
	 * @throws Exception
	 */
	public static void fillIn(ElectionSpecification es,String form,String pathToPrintsFile,Vector<Point> range,String[] chars, boolean charReset,String outDir) throws Exception {
		ContestSymbols cs=new ContestSymbols(pathToPrintsFile,es,chars,charReset);
		for (int i=0;i<range.size();i++) {
			for (int j=range.get(i).x;j<=range.get(i).y;j++) {
				fillIn(es,form,cs.getSerialNumber(j),cs.getAllSymbols(j,0),outDir+cs.getSerialNumber(j)+".pdf");
			}
		}
	}
	
	public static void fillIn(ElectionSpecification es,String form,String serial,String[] allSymbols,String output) throws FileNotFoundException, DocumentException, IOException {
		PdfReader reader = new PdfReader(form);
		
		PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(output));
		
        AcroFields form1 = stamp1.getAcroFields();
        
        int ii=0;
        while (form1.getField("serialTop_"+ii)!=null) {
        	ii++;
        }
        char bullet=162;
        serial=Util.AddleadingZeros(serial, ii);
        for (int i=0;i<serial.length();i++) {
        	form1.setField("serialTop_"+i,serial.charAt(i)+"");
        	form1.setField("serialBulleted_"+i+"_"+serial.charAt(i),Character.toString(bullet));
        }
        
        //set the serial in barcode
        form1.setField("serialBarcode", serial);
        
        Question[] qs=es.getOrderedQuestions();
        int count=0;
        for (int i=0;i<qs.length;i++) {
        	for (int j=0;j<qs[i].getAnswers().size();j++) {
    			form1.setField("bottomSymbol_"+i+"_"+0+"_"+j,allSymbols[count]);        			
    			form1.setFieldProperty("bottomSymbol_"+i+"_"+0+"_"+j,"setfflags",PdfFormField.Q_CENTER, null);
        		count++;
        	}
        }        
        stamp1.close();
	}
		
	public static void randomVote(FormMaker fm,String form) throws Exception {
		String javaScriptFromForm=fm.getJsInitValues()+fm.getJsFunctions();
		
		File f=new File(form);
		if (f.isFile()) {		
			PdfReader reader = new PdfReader(form);
			String output=form.substring(0,form.lastIndexOf(Util.fileSeparator)+1)+"Voted"+form.substring(form.lastIndexOf(Util.fileSeparator)+1);
			PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(output));
			StringBuffer sb=new StringBuffer("");
			
			Question[] qs=fm.getQs();
			int a;
			int r;
			for (int q=0;q<qs.length;q++) {
				r=0;
				for (int j=0;j<qs[q].getMax();j++) {
					if (Math.random()<0.9) {
						a =(int)(Math.random()*qs[q].getAnswers().size());
						if (qs[q].getTypeOfAnswer().compareTo(Constants.ONE_ANSWER)==0)
							sb.append("voteOne("+q+","+a+");");
						else
							if (qs[q].getTypeOfAnswer().compareTo(Constants.MULTIPLE_ANSWERS)==0)
								sb.append("voteMany("+q+","+a+");");
							else
								if (qs[q].getTypeOfAnswer().compareTo(Constants.RANK)==0)
									sb.append("voteRank("+q+","+r+","+a+");");
					}
					r++;
				}
			}
			
		    sb.append("finishSelection();");
		        
			stamp1.addJavaScript(javaScriptFromForm+sb.toString());
			stamp1.close();
		} else {
			File[] allFIles=f.listFiles();
			for (int i=0;i<allFIles.length;i++) {
				randomVote(fm, allFIles[i].getAbsolutePath());
			}
		}
	}

	//TODO a method that would construct a pdf similar with the scanned paper ballot
	public static void reconstructVote(FormMaker fm,String form, TreeMap<Integer, TreeMap<Integer, TreeMap<Integer, ScannedBallot.TypeOfVotes>>>  markedContests) throws Exception {
		String javaScriptFromForm=fm.getJsInitValues()+fm.getJsFunctions();
		
		File f=new File(form);
		if (f.isFile()) {		
			PdfReader reader = new PdfReader(form);
			String output=form.substring(0,form.lastIndexOf(Util.fileSeparator)+1)+"Voted"+form.substring(form.lastIndexOf(Util.fileSeparator)+1);
			PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(output));
			StringBuffer sb=new StringBuffer("");
			
			Question[] qs=fm.getQs();
			int a;
			int r;
			for (int q=0;q<qs.length;q++) {
				r=0;
				for (int j=0;j<qs[q].getMax();j++) {
					if (Math.random()<0.9) {
						a =(int)(Math.random()*qs[q].getAnswers().size());
						if (qs[q].getTypeOfAnswer().compareTo(Constants.ONE_ANSWER)==0)
							sb.append("voteOne("+q+","+a+");");
						else
							if (qs[q].getTypeOfAnswer().compareTo(Constants.MULTIPLE_ANSWERS)==0)
								sb.append("voteMany("+q+","+a+");");
							else
								if (qs[q].getTypeOfAnswer().compareTo(Constants.RANK)==0)
									sb.append("voteRank("+q+","+r+","+a+");");
					}
					r++;
				}
			}
			
		    sb.append("finishSelection();");
		        
			stamp1.addJavaScript(javaScriptFromForm+sb.toString());
			stamp1.close();
		} else {
			File[] allFIles=f.listFiles();
			for (int i=0;i<allFIles.length;i++) {
				randomVote(fm, allFIles[i].getAbsolutePath());
			}
		}
	}
	
	
	/**
	 * 
	 * @param args ElectionSpec PdfForm PrintsFile From0-To0;From1-To1 OutDir Chars
	 * @throws ESException
	 * @throws IOException
	 * @throws DocumentException
	 */
	public static void main(String[] args) throws Exception {
		String dir=InputConstants.publicFolder;
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");
		Vector<Point> range=new Vector<Point>();
		range.add(new Point(5,9));
		FillInPdfForm.fillIn(es, dir+"javaCreatedForm.pdf",InputConstants.privateFolder+"MeetingTwoPrints.xml",range,org.scantegrity.common.ContestSymbols.alphabet,false,dir);		
	}

}
