package org.scantegrity.common.auditing;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Hashtable;
import java.util.TreeMap;

import javax.xml.parsers.SAXParser;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.xml.sax.SAXException;

import com.itextpdf.text.pdf.AcroFields;
import com.itextpdf.text.pdf.PdfFormField;
import com.itextpdf.text.pdf.PdfReader;
import com.itextpdf.text.pdf.PdfStamper;

import org.scantegrity.common.ContestSymbols;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.MeetingReaderSax;
import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

public class RecordedAsCast {

	Hashtable<String, String> serialToPid=null;
	TreeMap<Integer,Prow> prows=null;
	
	String form=null;
	String outDir=null;

	ElectionSpecification es=null;
	
	ContestSymbols cs=null;
	
	public RecordedAsCast(String serialMap,String meetingThreeIn) throws SAXException, IOException {
		serialToPid=Util.SerialToPid(serialMap);
		
		MeetingReaderSax mr = new MeetingReaderSax();
        try {
            SAXParser saxParser = Util.newSAXParser();
            saxParser.parse( new File(meetingThreeIn), mr);
        } catch (Throwable t) {
            t.printStackTrace();
        }        
        while (!mr.isDoneParsing()) {
        	try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
        }        
		prows=mr.getProws();
	}
	
	public void recreateVotedBallot(String serial) throws Exception {
		//translate the serial to pid
		String pid=serialToPid.get(serial);
		
		Prow prow=prows.get(Integer.parseInt(pid));
		if (prow==null)
			throw new Exception("pid="+pid+" not found in m3in.xml");
		
		//create and save the ballot file
		PdfReader reader = new PdfReader(form);
		
		PdfStamper stamp1 = new PdfStamper(reader, new FileOutputStream(outDir+serial+".pdf"));
        AcroFields form1 = stamp1.getAcroFields();
        
        int ii=0;
        while (form1.getField("serialTop_"+ii)!=null) {
        	ii++;
        }
        
        boolean top;
        String serialField=null;
        if (prow.getChosenPage().equals(Prow.ChosenPage.TOP))
        	top=true;
        else
            if (prow.getChosenPage().equals(Prow.ChosenPage.BOTTOM))
            	top=false;
            else
            	throw new Exception("pid="+pid+"chosen page is neither top nor bottom. It is "+prow.getChosenPage());
        
        if (top)
        	serialField="serialTop_";
        else
        	serialField="serialBottom_";
        
        serial=Util.AddleadingZeros(serial, ii);
        //add the serial
        for (int i=0;i<serial.length();i++) {
        	form1.setField(serialField+i,serial.charAt(i)+"");
        }
        //TODO add the votes
        
        //add the symbols
        if (
        		(top&&prow.getPage1()!=null)
        		|| (!top&prow.getPage2()!=null)
        		)
        {
        	Question[] qs=es.getOrderedQuestions();
        	String[] allSymbols=null;
        	if (top)
        		allSymbols=cs.getAllSymbols(prow.getId(), 1);
        	else
        		allSymbols=cs.getAllSymbols(prow.getId(), 0);
	        int rows=1;
	        int count=0;
	        for (int i=0;i<qs.length;i++) {
	        	for (int j=0;j<qs[i].getAnswers().size();j++) {
	        		if (top)
	        			form1.setField("topSymbol_"+i+"_"+j,allSymbols[count]);
	        		if (!top) {
		        		rows=1;
		        		if (qs[i].getTypeOfAnswer().compareTo(Constants.RANK)==0) {
		        			rows=qs[i].getMax();
		        		}
		        		for (int k=0;k<rows;k++) {
		        			form1.setField("bottomSymbol_"+i+"_"+k+"_"+j,allSymbols[count]);        			
		        			form1.setFieldProperty("bottomSymbol_"+i+"_"+k+"_"+j,"setfflags",PdfFormField.Q_CENTER, null);
		        		}
	        		}
	        		count++;
	        	}
	        }
        }
        stamp1.close();		
	}

	public void addSymbols(String meetingThreeOut) throws Exception {
		//TODO parse m3out and set the permutations
		cs=new ContestSymbols(meetingThreeOut,es,ContestSymbols.alphabet,false);
	}
	
	public static void main(String[] args) throws Exception {

		String serial="0";
		
		RecordedAsCast rac=new RecordedAsCast(InputConstants.SerialMap,InputConstants.MeetingThreeIn);
		rac.recreateVotedBallot(serial);

	}

}
