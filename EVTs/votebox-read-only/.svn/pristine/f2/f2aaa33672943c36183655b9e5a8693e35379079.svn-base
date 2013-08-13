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

package preptool.model.layout;

/**
 * A visitor interface over the ALayoutComponent composite.
 * @param <P> the parameter type
 * @param <R> the return type
 * @author cshaw
 */
public interface ILayoutComponentVisitor<P,R> {
	
	/**
	 * Background case
	 * @param bg the Background
	 * @param param parameters
	 * @return the result
	 */
	public R forBackground(Background bg, P... param);
	
	/**
	 * Button case
	 * @param b the Button
	 * @param param parameters
	 * @return the result
	 */
	public R forButton(Button b, P... param);
	
	/**
	 * Label case
	 * @param l the Label
	 * @param param parameters
	 * @return the result
	 */
	public R forLabel(Label l, P... param);
	
	/**
	 * ReviewButton case
	 * @param rb the ReviewButton
	 * @param param parameters
	 * @return the result
	 */
	public R forReviewButton(ReviewButton rb, P... param);
	
	/**
	 * ReviewLabel case
	 * @param rl the ReviewLabel
	 * @param param parameters
	 * @return the result
	 */
	public R forReviewLabel(ReviewLabel rl, P... param);
	
	/**
	 * ToggleButton case
	 * @param tb the ToggleButton
	 * @param param parameters
	 * @return the result
	 */
	public R forToggleButton(ToggleButton tb, P... param);
	
	/**
	 * ToggleButtonGroup case
	 * @param tbg the ToggleButtonGroup
	 * @param param parameters
	 * @return the result
	 */
	public R forToggleButtonGroup(ToggleButtonGroup tbg, P... param);
	
	/**
	 * Renders a VVPAT compatible verison of the ReviewButton
	 * @param rb the ReviewButton
	 * @param param the parameters
	 * @return the result
	 */
	public R forVVPATReviewButton(ReviewButton rb, P... param);
	

}
