package org.scantegrity.common;

import java.io.File;
import java.util.TreeMap;
import java.util.Vector;

import javax.xml.parsers.SAXParser;

import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;



/**
 * Permutes the symbols as they should appear on each ballot.
 * 
 * Given the prints file (produced by m2), and the serial number of a ballot
 * it produces the entire set of permuted symbols in the order they appear on a ballot
 * (both top and bottom pages)
 * @author stefan
 */
public class ContestSymbols {

	public static String[] alphabet = { "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "R", "S", "T", "U", "W", "X", "Y" };

	protected String[] allSymbols=null;
	
	protected TreeMap<Integer,Prow> prows=null;
	protected Question[] qs=null;
	
	/** 
	 * @param pathToPrintsFile - path to the files produced in meting 2, specifiyng the permutation on each ballot
	 * @param pathToElectionSpec - path to a file containing the ElectionSpec
	 * @param chars - The charachters to be permuted (that appear on the ballot)
	 * There is either one carachter and that is "A" or "a" or "0", or there are
	 * at least as many charachters as the biggest contest. 
	 * @param charReset - true if every contest should start from the first charachter, 
	 * false if the first character of a contest is the next character in the array.
	 * @throws Exception
	 */
	public ContestSymbols(String pathToPrintsFile,String pathToElectionSpec,String[] chars,boolean charReset) throws Exception {
		this(pathToPrintsFile, new ElectionSpecification(pathToElectionSpec),chars,charReset);
	}

	/** 
	 * @param pathToPrintsFile - path to the files produced in meting 2, specifiyng the permutation on each ballot
	 * @param es - the ELection Specification
	 * @param chars - The charachters to be permuted (that appear on the ballot)
	 * There is either one carachter and that is "A" or "a" or "0", or there are
	 * at least as many charachters as the biggest contest. 
	 * @param charReset - true if every contest should start from the first charachter, 
	 * false if the first character of a contest is the next character in the array.
	 * @throws Exception
	 */
	public ContestSymbols(String pathToPrintsFile,ElectionSpecification es,String[] chars,boolean charReset) throws Exception {
		
		qs = es.getOrderedQuestions();		
		
		int maxNoOfCandidates = 0;
		for (int i=0;i<qs.length;i++) {
			if (maxNoOfCandidates < qs[i].getAnswers().size() ) {
				maxNoOfCandidates = qs[i].getAnswers().size();
			}
		}
		
		if (chars.length == 1) {
			String start = chars[0];
			if (start!="A" && start!="a" && start!="0")
				throw new Exception("The symbol character has to be \'A\' or \'a\' or \'0\'");
				
			chars = new String[maxNoOfCandidates];
			for (int i=0;i<maxNoOfCandidates;i++) {
				chars[i]=Character.toString((char)(start.charAt(0)+i));
			}
		} else {
			if (chars.length < maxNoOfCandidates) {
				throw new Exception("the number of symbols provided is smaller then the number of candidates in the biggest contest");
			}
		}
					

		Vector<String> allSymbolsVector=new Vector<String>(); 
		
		int charsPoz=0;
		int numberOfAnswers = 0;
		for (int i=0;i<qs.length;i++) {
			numberOfAnswers = qs[i].getAnswers().size();		
			if (charReset || charsPoz+numberOfAnswers>chars.length)
				charsPoz=0;
			for (int j=0;j<numberOfAnswers;j++) {
				allSymbolsVector.add(chars[charsPoz++]);
				if (charsPoz>=chars.length)
					charsPoz = 0;
			}		
		}

		allSymbols =new String[allSymbolsVector.size()];
		int pos=0;
		for (String s:allSymbolsVector)
			allSymbols[pos++]=s;
		
		if (pathToPrintsFile!=null) {
			MeetingReaderSax mr = new MeetingReaderSax();
	        try {
	            SAXParser saxParser = Util.newSAXParser();
	            saxParser.parse( new File(pathToPrintsFile), mr);
	        } catch (Throwable t) {
	            t.printStackTrace();
	        }        
	        while (!mr.isDoneParsing()) {
	        	Thread.sleep(100);
	        }        
			prows=mr.getProws();
		}
	}
	
	/**
	 * @param r - the row number in the prints file
	 * @return - the serial number of row number r in the prints file
	 */	 	
	public String getSerialNumber(int r) {
		return prows.get(r).getId()+""; 
	}

	/**
	 * returns all the symbols (permuted for each contest) for serial number r and the given page
	 * @param r - the row number in the prints table
	 * @param page - 0 or 1 corresponding to bottom or top
	 * @return a String of permuted characters (per contest)
	 * @throws Exception 
	 */
	public String[] getAllSymbols(int r,int page) throws Exception {
		return getAllSymbols(prows.get(r), page,allSymbols);
	}

	public String[] getAllSymbols(Prow prow,int page,String[] allSymbols) throws Exception {
		String[] ret=new String[allSymbols.length];
		
		int numberOfAnswers = 0;
		
		if (prow!=null) {
			int numberOfAnswersUntillCurrentQuestion = 0;			
			for (int i=0;i<qs.length;i++) {
				numberOfAnswers = qs[i].getAnswers().size();
				byte[] perm = getPermutationForCurrentPage(prow.getPage1(), prow.getPage2(), numberOfAnswers, numberOfAnswersUntillCurrentQuestion, page);
				Util.permString(perm,allSymbols,numberOfAnswersUntillCurrentQuestion,ret);				
				numberOfAnswersUntillCurrentQuestion+=numberOfAnswers;				
			}
		}
		return ret;
	}
	
	protected byte[] getPermutationForCurrentPage(byte[] p1, byte[] p2,int numberOfAnswers,int numberOfAnswersUntillCurrentQuestion, int page ) {
		byte[] perm = new byte[numberOfAnswers];
		if (page==1) {
			System.arraycopy(p1,numberOfAnswersUntillCurrentQuestion,perm,0,numberOfAnswers);										
		} else {
			if (page==0) {
				System.arraycopy(p2,numberOfAnswersUntillCurrentQuestion,perm,0,numberOfAnswers);				
			}
		}
		return perm;
	}
	
	/**
	 * @return - the symbols on the canonical ballot
	 */	
	public String[] getCanonicalSymbols() {
		return allSymbols;
	}
	
	/**
	 * Debug method
	 * @param args
	 * @throws Exception
	 */
	public static void main(String[] args) throws Exception{
		String[] chars={"A","B","C"};
		ContestSymbols cs = new ContestSymbols(args[0],args[1],chars,true);
		System.out.println(cs.getAllSymbols(0,0));
		System.out.println(cs.getAllSymbols(0,1));
	}
}
