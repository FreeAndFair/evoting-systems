/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package preptool.model.language;

import java.util.HashMap;

/**
 * A class that contains literal localized strings used by the LayoutManager, so
 * that it can output the correct strings based on the language.
 * @author cshaw
 */
public class LiteralStrings {

	/**
	 * Singleton pattern.
	 */
	public static final LiteralStrings Singleton = new LiteralStrings();

	/**
	 * Singleton pattern - private constructor.<br>
	 * Initalizes the hash map with all of the LocalizedStrings (later will load
	 * from files)
	 */
	private LiteralStrings() {
		map = new HashMap<String, LocalizedString>();
		
		HashMap<String, Language> langs = new HashMap<String, Language>();
		for (Language lang: Language.getAllLanguages())
			langs.put(lang.getName(), lang);
		Language ENGLISH = langs.get("English");
		Language SPANISH = langs.get("Spanish");
		
		LocalizedString ls = new LocalizedString();
		ls.set(ENGLISH, "Instructions \n ");
		ls.set(SPANISH, "Instrucciónes \n ");
		map.put("INSTRUCTIONS_TITLE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Review Choices \n ");
		map.put("REVIEW_TITLE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Record Vote \n ");
		map.put("RECORD_TITLE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Thank you for voting!");
		map.put("SUCCESS_TITLE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "You must make a selection!");
		map.put("NO_SELECTION_TITLE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "You must make a selection on every page. If you do not want to vote, select 'None of the above'.");
		map.put("NO_SELECTION", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go back to the selection screen");
		map.put("RETURN_RACE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "None of the Above");
		ls.set(SPANISH, "Ninguna de las Anteriores");
		map.put("NONE_OF_ABOVE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Thank you for challenging!");
		map.put("RESPONSE_TITLE", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Language Selection");
        map.put("LANGUAGE_SELECT_TITLE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Record Vote");
		map.put("CAST_BUTTON", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Next Page" + '\u2192');
		map.put("COMMIT_BUTTON", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Challenge Vote");
		map.put("CHALLENGE_BUTTON", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Next Page" + '\u2192');
		map.put("NEXT_PAGE_BUTTON", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, '\u2190' + "Previous Page");
		map.put("PREVIOUS_PAGE_BUTTON", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Return");
		map.put("RETURN_BUTTON", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n STEP 1 \n Read Instructions");
		map.put("SIDEBAR_INSTRUCTIONS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n STEP 2 \n Make your choices");
		map.put("SIDEBAR_MAKE_CHOICES", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n STEP 3 \n Review your choices");
		map.put("SIDEBAR_REVIEW_CHOICES", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n STEP 4 \n Record your vote");
		map.put("SIDEBAR_RECORD_VOTE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n You are now on \n STEP 1 \n Read Instructions");
		map.put("SIDEBAR_INSTRUCTIONS_HIGHLIGHTED", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n You are now on \n STEP 2 \n Make your choices");
		map.put("SIDEBAR_MAKE_CHOICES_HIGHLIGHTED", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n You are now on \n STEP 3 \n Review your choices");
		map.put("SIDEBAR_REVIEW_CHOICES_HIGHLIGHTED", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n You are now on \n STEP 4 \n Record your vote");
		map.put("SIDEBAR_RECORD_VOTE_HIGHLIGHTED", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go foward to next race");
		map.put("FORWARD_NEXT_RACE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go back to previous race");
		map.put("BACK_PREVIOUS_RACE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to see more candidates");
		map.put("MORE_CANDIDATES", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go back to the review screen");
		map.put("RETURN_REVIEW_SCREEN", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go back to Instructions");
		map.put("BACK_INSTRUCTIONS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go to Step 3: Review your choices");
		map.put("FORWARD_REVIEW", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go back to Step 3: Review your choices");
		map.put("BACK_REVIEW", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to record your vote");
		map.put("FORWARD_SUCCESS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go to Step 2: Make your choices");
		map.put("FORWARD_FIRST_RACE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go back to Step 2: Make your choices");
		map.put("BACK_LAST_RACE", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Click to go to Step 4: Record your vote");
		map.put("FORWARD_RECORD", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Click to go back to Language Selection");
        map.put("BACK_LANGUAGE_SELECT", ls);

        ls = new LocalizedString();
        ls.set(ENGLISH, "Click to go to Step 1: Instructions");
        map.put("FORWARD_INSTRUCTIONS", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "To make your choice, click on the candidate's name or on the box next to his/her "
				+ "\n name. A green checkmark will appear next to your choice. If you want to change "
				+ "\n your choice, just click on a different candidate or box.");
		map.put("RACE_INSTRUCTIONS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "Below are the choices you have made. If you would like to make changes, click on the race you would "
				+ "\n like to change. If you do not want to make changes,"
				+ "\n click the 'Next Page' button to go to Step 4. "
				+ "\n **Your vote will not be recorded unless you finish step 4.**");
		map.put("REVIEW_INSTRUCTIONS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n Welcome. You are about to begin voting in a mock election at Rice University. "
				+ "\n \n There are four steps to voting in this election. "
				+ "\n \n Step 1: Finish reading Instructions. "
				+ "\n \n Step 2: Make your choice. This is where you will choose your candidates "
				+ "\n and vote for or against the propositions. You will make one choice per page. "
				+ "\n \n Step 3: Review your choices. This is where you will see all the choices you "
				+ "\n have made and be able to make any changes you want. "
				+ "\n \n Step 4: Record your vote by clicking on the 'Record Vote' button. This is the "
				+ "\n last step. Once you finish this step, you will not be able to make any changes, "
				+ "\n and your vote will be recorded. "
				+ "\n \n When you get to each of these four steps, you will see more detailed "
				+ "\n instructions. "
				+ "\n \n At the bottom of the screen, there will be buttons you can click with your "
				+ "\n mouse. Click the 'Next Page' button to go to the next page.");
		map.put("INSTRUCTIONS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "You can not make any changes once you click the 'Next Page' "
				+ "\n button. When you click the button, your vote will be officially "
				+ "\n recorded. "
				+ "\n \n If you want to make changes, click the 'Previous Page' button to "
				+ "\n go back to the Review Screen. ");
		map.put("RECORD_INSTRUCTIONS", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Please select the language you would like to vote in.");
        map.put("LANGUAGE_SELECT_INSTRUCTIONS", ls);

		ls = new LocalizedString();
		ls.set(ENGLISH, "\n Your vote has been recorded. You may now leave the voting booth. ");
		map.put("SUCCESS", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "\n Your vote has not been recorded. Please re-authorize this booth to cast your vote. ");
		map.put("RESPONSE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Yes");
		ls.set(SPANISH, "Si");
		map.put("YES", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "No");
		ls.set(SPANISH, "No");
		map.put("NO", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "None");
		ls.set(SPANISH, "Nada");
		map.put("NONE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "Page");
		ls.set(SPANISH, "Pagina");
		map.put("PAGE", ls);
		
		ls = new LocalizedString();
		ls.set(ENGLISH, "of");
		ls.set(SPANISH, "de");
		map.put("OF", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Override Cancel");
        map.put("OVERRIDE_CANCEL_TITLE", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "The election supervisor has requested that this ballot be cancelled. \n Proceed with this operation?");
        map.put("OVERRIDE_CANCEL_INSTRUCTIONS", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Yes, Cancel this Ballot");
        map.put("OVERRIDE_CANCEL_CONFIRM", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Override Cast");
        map.put("OVERRIDE_CAST_TITLE", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "The election supervisor has requested that this ballot be cast. \n Proceed with this operation?");
        map.put("OVERRIDE_CAST_INSTRUCTIONS", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Yes, Cast this Ballot");
        map.put("OVERRIDE_CAST_CONFIRM", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "No, Ignore this Request");
        map.put("OVERRIDE_DENY", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Challenge");
        map.put("CHALLENGE_TITLE", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "You have the option of challenging the VoteBox. \n Do you wish to challenge this VoteBox?");
        map.put("CHALLENGE_INSTRUCTIONS", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "Yes, Challenge this VoteBox");
        map.put("CHALLENGE_CONFIRM", ls);
        
        ls = new LocalizedString();
        ls.set(ENGLISH, "No, Cast my Ballot");
        map.put("CHALLENGE_DENY", ls);
	}

	/**
	 * The map holding all of the strings
	 */
	private HashMap<String, LocalizedString> map;

	/**
	 * Returns the string for the given key and language
	 * @param key the key for the string
	 * @param lang the language
	 * @return the translated string
	 */
	public String get(String key, Language lang) {
		LocalizedString ls = map.get(key);
		if (ls == null)
			throw new IllegalArgumentException("String not found");
		else
			return ls.get(lang);
	}
    
	/**
	 * Returns the LocalizedString for the given key
	 * @param key the key for the string
	 * @return the LocalizedString
	 */
    public LocalizedString get(String key) {
    	LocalizedString ls = map.get(key);
		if (ls == null)
			throw new IllegalArgumentException("String not found");
		else
			return ls;
    }

}
