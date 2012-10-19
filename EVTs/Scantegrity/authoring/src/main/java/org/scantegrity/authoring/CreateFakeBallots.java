package org.scantegrity.authoring;


import java.io.FileNotFoundException;
import java.io.IOException;

import java.util.Collections;
import java.util.Vector;


import org.scantegrity.common.ballotstandards.basic.Question;
import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.ContestSymbols;
import org.scantegrity.common.Prow;


import com.itextpdf.text.DocumentException;

public class CreateFakeBallots extends FillInPdfForm {

	static void createFakeBallot(ElectionSpecification es,String form,String serial, Prow.ChosenPage page,String[] allSymbolsOnTheSelectedPage, byte[] encVote, byte[] clearVote,String output) throws FileNotFoundException, DocumentException, IOException {
		//create the symbols on the other page
		String[] allTopSymbols=null;
		String[] allBottomSymbols=null;

		if (page.equals(Prow.ChosenPage.TOP)) {
			allBottomSymbols=createFakeBottomSymbols(es,allSymbolsOnTheSelectedPage,encVote,clearVote);
			allTopSymbols=allSymbolsOnTheSelectedPage;
		} else {
			if (page.equals(Prow.ChosenPage.BOTTOM)) {
				allTopSymbols=createFakeTopSymbols(es,allSymbolsOnTheSelectedPage,encVote,clearVote);
				allBottomSymbols=allSymbolsOnTheSelectedPage;
			}
		}
		fillIn(es, form, serial, allTopSymbols, allBottomSymbols, output);
	}
	
	static String[] createFakeBottomSymbols(ElectionSpecification es,String[] topSymbols,byte[] encVote,byte[] clearVote)  {
		String[] fakeBottomSymbols=new String[topSymbols.length];
		
        Question[] qs=es.getOrderedQuestions();
        int encVotePos=0;
        int topSymbolsPos=0;
        for (int i=0;i<qs.length;i++) {
        	Vector<String> allCodes=new Vector<String>(qs[i].getAnswers().size());
        	for (int j=0;j<qs[i].getAnswers().size();j++) {
        		allCodes.add(topSymbols[topSymbolsPos+j]);
        	}
        	
        	for (int j=0;j<qs[i].getMax();j++) {
        		if (encVote[encVotePos+j]!=-1) {
        			String symbol=topSymbols[topSymbolsPos+clearVote[encVotePos+j]];
        			allCodes.remove(symbol);
        			fakeBottomSymbols[topSymbolsPos+encVote[encVotePos+j]]=symbol;
        		}
        	}
        	
        	Collections.shuffle(allCodes);
        	
        	//add the rest of the letters
        	for (int j=0;j<qs[i].getAnswers().size();j++) {
        		if (fakeBottomSymbols[topSymbolsPos+j]==null) {
        			fakeBottomSymbols[topSymbolsPos+j]=allCodes.firstElement();
        			allCodes.remove(0);
        		}
        	}
        	topSymbolsPos+=qs[i].getAnswers().size();
        	encVotePos+=qs[i].getMax();
        }        

		return fakeBottomSymbols;
	}

	static String[] createFakeTopSymbols(ElectionSpecification es,String[] bottomSymbols,byte[] encVote,byte[] clearVote)  {
		return createFakeBottomSymbols(es, bottomSymbols, clearVote,encVote);
	}

	public static void main(String[] args) throws Exception {
		String dir="Elections/Crypto08/CPSR_Style/";
		ElectionSpecification es=new ElectionSpecification(dir+"ElectionSpec.xml");
		String[] allSymbols=null;
		byte[] encVote={-1,-1,-1,3,0,4,1};
		byte[] clearVote={-1,-1,-1,0,1,5,0};
		
		String pathToPrintsFile=dir+"MeetingTwoPrints.xml";
		ContestSymbols cs=new ContestSymbols(pathToPrintsFile,es,ContestSymbols.alphabet,false);
		
		int serial=1048;
		
		Prow.ChosenPage page=Prow.ChosenPage.BOTTOM;
		
		if (page.equals(Prow.ChosenPage.TOP)) {
			allSymbols=cs.getAllSymbols(serial, 1);
		} else {
			if (page.equals(Prow.ChosenPage.BOTTOM)) {
				allSymbols=cs.getAllSymbols(serial, 0);
			}
		}
		
		createFakeBallot(es, dir+"javaCreatedForm.pdf", serial+"", page, allSymbols, encVote, clearVote, dir+"fake"+serial+".pdf");
	}

}
