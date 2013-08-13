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

package preptool.view;

import preptool.model.language.Language;

/**
 * An interface that links with a LanguageBar.  The LanguageBar uses this interface
 * to inform the editor that the language has been changed or to check if all
 * translation data exists.
 * @author cshaw
 */
public interface IMultiLanguageEditor {
	
	/**
	 * Method that is called by a LanguageBar when a language has been selected
	 * @param lang the language
	 */
	public void languageSelected(Language lang);
	
	/**
	 * Checks if the editor has all translation information filled in for the
	 * given language
	 * @param lang the language
	 * @return whether all translation info is entered
	 */
	public boolean needsTranslation(Language lang);
	
	/**
	 * Called by a LanguageBar when the primary language has changed
	 * @param lang the language
	 */
	public void updatePrimaryLanguage(Language lang);
	
}
