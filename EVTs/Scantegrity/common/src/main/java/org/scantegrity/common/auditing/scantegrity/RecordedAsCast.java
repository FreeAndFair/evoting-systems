package org.scantegrity.common.auditing.scantegrity;

import java.util.Hashtable;

import org.scantegrity.common.scantegrity.ContestSymbols;
import org.scantegrity.common.InputConstants;
import org.scantegrity.common.Util;

//This class is for the Java servlet to serve to the voters on a web page
public class RecordedAsCast {

	Hashtable<String, String> serialToPid=null;
	ContestSymbols cs=null;
	
	static RecordedAsCast instance=null;
	
	public static RecordedAsCast getInstance(String serialMap,String meetingThreeIn, String es) throws Exception {
		if (instance==null) {
			instance=new RecordedAsCast(serialMap,meetingThreeIn,es);
		}
		return instance;	
	}
	
	private RecordedAsCast(String serialMap,String meetingThreeIn, String es) throws Exception {
		serialToPid=Util.SerialToPid(serialMap);
		cs=new ContestSymbols(meetingThreeIn,es, ContestSymbols.alphabet,false);
	}
	
	public String[] getLetters(String serial) throws Exception {
		String pid=serialToPid.get(serial);
		
		return cs.getSelectedSymbols(pid);
	}
	
	public static void main(String args[]) throws Exception {
		RecordedAsCast rac=new RecordedAsCast(InputConstants.SerialMap,InputConstants.MeetingThreeIn,InputConstants.ElectionSpec);
		String letters[]=rac.getLetters(15+"");
		for (int i=0;i<letters.length;i++)
			System.out.println(letters[i]+";");
	}
}
