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

package votebox.middle.view;

/**
 * This exception is thrown when a language is required that is not supported.
 * 
 * @author Kyle
 * 
 */
public class UnsupportedLanguageException extends Exception {

	/**
	 * default serial version uid.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This is the language that isn't supported.
	 */
	private String _language;
	
	/**
	 * This is the public constructor for UnsupportedLanguageException
	 * 
	 * @param language
	 *            This is the language that isn't supported.
	 */
	public UnsupportedLanguageException(String language) {
		super(language + "is not supported in this ballot.");
		_language = language;
	}
	
	/**
	 * This is the getter for _language.
	 * @return _language.
	 */
	public String getLanguage(){
		return _language;
	}
}