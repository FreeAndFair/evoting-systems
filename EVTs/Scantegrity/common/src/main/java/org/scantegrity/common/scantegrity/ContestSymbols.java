package org.scantegrity.common.scantegrity;

import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

public class ContestSymbols extends org.scantegrity.common.ContestSymbols {

	int maxNoA=-1;
	
	public ContestSymbols(String pathToPrintsFile, String pathToElectionSpec, String[] chars, boolean charReset) throws Exception {
		super(pathToPrintsFile, pathToElectionSpec, chars, charReset);
		setMaxNoA();
	}

	public ContestSymbols(String pathToPrintsFile, ElectionSpecification es, String[] chars, boolean charReset) throws Exception {
		super(pathToPrintsFile, es, chars, charReset);
		setMaxNoA();
	}
	
	protected void setMaxNoA() {
		maxNoA=0;
		for (int i=0;i<qs.length;i++) {
        	maxNoA+=qs[i].getMax();
		}
	}
	
	public String[] getSelectedSymbols(String pid) throws Exception {
		Prow prow=prows.get(Integer.parseInt(pid));
		if (prow==null)
			throw new Exception("pid="+pid+" not found in m3in.xml");
		
		byte[] vote=prow.getVote();
		
		String[] ret=new String[maxNoA];
		int retPos=0;
		int allSymbolsPos=0;
		for (int i=0;i<qs.length;i++) {
        	for (int j=0;j<qs[i].getMax();j++) {
        		if (vote[retPos]==-1) {
        			ret[retPos]=" ";
        		} else {
        			ret[retPos]=allSymbols[allSymbolsPos+vote[retPos]];
        		}
        		retPos++;
        	}
        	allSymbolsPos+=qs[i].getAnswers().size();
		}
		return ret;
	}
	
	protected byte[] getPermutationForCurrentPage(byte[] p1, byte[] p2,int numberOfAnswers,int numberOfAnswersUntillCurrentQuestion, @SuppressWarnings("unused")
	int page ) {
		byte[] ret = new byte[numberOfAnswers];
		
		byte[] permTop = new byte[numberOfAnswers];
		System.arraycopy(p1,numberOfAnswersUntillCurrentQuestion,permTop,0,numberOfAnswers);
		byte[] permBottom = new byte[numberOfAnswers];
		System.arraycopy(p2,numberOfAnswersUntillCurrentQuestion,permBottom,0,numberOfAnswers);
		byte[] permBottomInverse=Util.getInverse(permBottom);
		for (int j=0;j<permTop.length;j++) {
			ret[j]=permBottomInverse[permTop[j]];				
		}
		return ret;
	}

}
