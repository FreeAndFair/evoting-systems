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

import java.awt.Dimension;

/**
 * A special type of Label that is seen on review screens.
 * @author cshaw
 */
public class ReviewLabel extends Label {

	/**
	 * Constructs a ReviewLabel with the given unique ID, text, and strategy.
	 * @param uid the unique ID
	 * @param text the text
	 */
	public ReviewLabel(String uid, String text) {
		super(uid, text);
	}

	/**
	 * Constructs a ReviewButton with the given unique ID, text, strategy, and
	 * size visitor that determines and sets the size.
	 * @param uid the unique ID
	 * @param text the text
	 * @param sizeVisitor the size visitor
	 */
	public ReviewLabel(String uid, String text,
			ILayoutComponentVisitor<Object,Dimension> sizeVisitor) {
		this(uid, text);
		setSize(execute(sizeVisitor));
	}

	/**
	 * Calls the forReviewButton method in visitor
	 * @param visitor the visitor
	 * @param param the parameters
	 * @return the result of the visitor
	 */
	@Override
	public <P,R> R execute(ILayoutComponentVisitor<P,R> visitor, P... param) {
		return visitor.forReviewLabel(this, param);
	}

}
