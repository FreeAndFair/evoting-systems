package org.scantegrity.authoring.invisibleink;

import org.scantegrity.common.ballotstandards.Constants;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.Prow;
import org.scantegrity.common.Util;

public class ContestSymbols extends
		org.scantegrity.common.scantegrity.ContestSymbols {
	
	public ContestSymbols(String pathToPrintsFile, String pathToElectionSpec, String[] chars, boolean charReset) throws Exception {
		super(pathToPrintsFile, pathToElectionSpec, chars, charReset);
	}

	public ContestSymbols(String pathToPrintsFile, ElectionSpecification es, String[] chars, boolean charReset) throws Exception {
		super(pathToPrintsFile, es, chars, charReset);
	}

	public String[] getAllSymbols(Prow prow,int page,String[] allSymbols) throws Exception {
		String[] ret=new String[allSymbols.length];
		
		int numberOfAnswers = 0;
		
		if (prow!=null) {
			int numberOfCodesUntillCurrentQuestion = 0;			
			int numberOfAnswersUntillCurrentQuestion = 0;
			for (int i=0;i<qs.length;i++) {
				numberOfAnswers = qs[i].getAnswers().size();
				byte[] perm = getPermutationForCurrentPage(prow.getPage1(), prow.getPage2(), numberOfAnswers, numberOfAnswersUntillCurrentQuestion, page);

				
				if ( ! qs[i].getTypeOfAnswer().equals(Constants.RANK)) {
					Util.permString(perm,allSymbols,numberOfCodesUntillCurrentQuestion,ret);
					numberOfCodesUntillCurrentQuestion+=numberOfAnswers;
				} else {				
					//if (qs[i].getTypeOfAnswer().equals(Constants.RANK))
						int chunkSize=qs[i].getMax();
						Util.permString(perm,allSymbols,numberOfCodesUntillCurrentQuestion,ret, chunkSize);
						numberOfCodesUntillCurrentQuestion+=numberOfAnswers*chunkSize;
				}
				numberOfAnswersUntillCurrentQuestion+=numberOfAnswers;						
			}
		}
		return ret;
	}
}
