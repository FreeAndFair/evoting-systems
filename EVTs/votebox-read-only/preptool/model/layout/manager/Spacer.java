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

package preptool.model.layout.manager;

import java.awt.Container;
import java.awt.Dimension;

import javax.swing.JLabel;

import preptool.model.layout.ALayoutComponent;


/**
 * A Spacer is a holder for an ALayoutComponent, but it also subclasses JLabel
 * so that it can be placed onto a JPanel. This allows Swing to layout our
 * components for us.
 * @author cshaw, ttorous
 */
@SuppressWarnings("serial")
public class Spacer extends JLabel {

	/**
	 * The component held by this Spacer
	 */
	private ALayoutComponent comp;

	/**
	 * The container holding this Spacer
	 */
	private Container par;

	/**
	 * Creates an Spacer with the given component and container, and sets its
	 * size to the size of the component.<br>
	 * Warning: The size of the component must be set properly before
	 * constructing the Spacer, or it will be initialized improperly!
	 * @param lc the LayoutComponent this corresponds to
	 * @param container the Container that holds this Spacer
	 */
	public Spacer(ALayoutComponent lc, Container container) {
		setMinimumSize(new Dimension(lc.getWidth(), lc.getHeight()));
		setPreferredSize(new Dimension(lc.getWidth(), lc.getHeight()));
		setMaximumSize(new Dimension(lc.getWidth(), lc.getHeight()));
		setSize(new Dimension(lc.getWidth(), lc.getHeight()));

		comp = lc;
		par = container;
		validate();
	}

	/**
	 * Returns the component
	 * @return the component
	 */
	public ALayoutComponent getComponent() {
		return comp;
	}

	/**
	 * Returns the absolute X coordinate. Simply calling getX will not work
	 * because this returns the relative x coordinate of the label to its
	 * parent. This implementation assumes that the parent only goes one layer
	 * up
	 * @return the absolute X coordintate
	 */
	public int getXCoordinate() {
		return par.getX() + getX();
	}

	/**
	 * See getXCoordinate
	 * @return the absolute Y coordinte
	 */
	public int getYCoordinate() {
		return par.getY() + getY();
	}

	/**
	 * Updates the x and y coordinates of the component's position based on the
	 * spacer's position
	 */
	public void updatePosition() {
		comp.setXPos(getXCoordinate());
		comp.setYPos(getYCoordinate());
	}

}
