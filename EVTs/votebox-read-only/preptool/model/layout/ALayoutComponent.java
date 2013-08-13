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


import org.w3c.dom.Document;
import org.w3c.dom.Element;

import preptool.model.XMLTools;

/**
 * ALayoutComponent is the abstract notion of anything that belongs on a Page,
 * that is anything that can be laid out and displayed on the screen, including
 * labels, buttons, and toggle buttons. An ALayoutComponent records its size and
 * position, and the relative position of other ALayoutComponents on the page.
 * @author cshaw
 */
public abstract class ALayoutComponent implements Cloneable {

	/**
	 * The width of this component
	 */
	protected int width;

	/**
	 * The height of this component
	 */
	protected int height;

	/**
	 * The x-coordinate of this component's position
	 */
	protected int xPos;

	/**
	 * The y-coordinate of this component's position
	 */
	protected int yPos;

	/**
	 * The unique ID of this component, assigned by the LayoutManager
	 */
	protected String uniqueID;

	/**
	 * The component (if any) above this component
	 */
	protected ALayoutComponent up;

	/**
	 * The component (if any) below this component
	 */
	protected ALayoutComponent down;

	/**
	 * The component (if any) to the left of this component
	 */
	protected ALayoutComponent left;

	/**
	 * The component (if any) to the right of this component
	 */
	protected ALayoutComponent right;

	/**
	 * The component (if any) that is next in sequence of this component
	 */
	protected ALayoutComponent next;

	/**
	 * The component (if any) that is previous in sequence of this component
	 */
	protected ALayoutComponent previous;
	
	/**
	 * Creates a new ALayoutComponent with the given unique ID
	 * @param uniqueID the unique ID
	 */
	public ALayoutComponent(String uniqueID) {
		super();
		this.uniqueID = uniqueID;
	}

	/**
	 * Clones this component, keeping the same parameters (including UID)<br>
	 * Used so that two of the same component can be on the same page, but in
	 * different locations
	 */
	@Override
    public ALayoutComponent clone() {
		try {
			return (ALayoutComponent)super.clone();
		} catch (CloneNotSupportedException e) {
			e.printStackTrace();
		}
		return null;
	}
	
	/**
	 * Executes an ILayoutComponentVisitor on this component.
	 * @param visitor the visitor
	 * @param param the parameters
	 * @return the result of the visitor
	 */
	public abstract <P,R> R execute(ILayoutComponentVisitor<P,R> visitor, P... param);

	/**
	 * @return the down
	 */
	public ALayoutComponent getDown() {
		return down;
	}

	/**
	 * @return the height
	 */
	public int getHeight() {
		return height;
	}

	/**
	 * @return the left
	 */
	public ALayoutComponent getLeft() {
		return left;
	}

	/**
	 * @return the next
	 */
	public ALayoutComponent getNext() {
		return next;
	}

	/**
	 * @return the previous
	 */
	public ALayoutComponent getPrevious() {
		return previous;
	}

	/**
	 * @return the right
	 */
	public ALayoutComponent getRight() {
		return right;
	}

	/**
	 * @return the unique ID
	 */
	public String getUID() {
		return uniqueID;
	}

	/**
	 * @return the up
	 */
	public ALayoutComponent getUp() {
		return up;
	}

	/**
	 * @return the width
	 */
	public int getWidth() {
		return width;
	}

	/**
	 * @return the xPos
	 */
	public int getXPos() {
		return xPos;
	}

	/**
	 * @return the yPos
	 */
	public int getYPos() {
		return yPos;
	}

	/**
	 * @param down the down to set
	 */
	public void setDown(ALayoutComponent down) {
		this.down = down;
	}

	/**
	 * @param height the height to set
	 */
	public void setHeight(int height) {
		this.height = height;
	}

	/**
	 * @param left the left to set
	 */
	public void setLeft(ALayoutComponent left) {
		this.left = left;
	}

	/**
	 * @param next the next to set
	 */
	public void setNext(ALayoutComponent next) {
		this.next = next;
	}

	/**
	 * @param previous the previous to set
	 */
	public void setPrevious(ALayoutComponent previous) {
		this.previous = previous;
	}

	/**
	 * @param right the right to set
	 */
	public void setRight(ALayoutComponent right) {
		this.right = right;
	}

	/**
	 * @param dim the size to set
	 */
	public void setSize(Dimension dim) {
		width = dim.width;
		height = dim.height;
	}

	/**
	 * @param up the up to set
	 */
	public void setUp(ALayoutComponent up) {
		this.up = up;
	}

	/**
	 * @param width the width to set
	 */
	public void setWidth(int width) {
		this.width = width;
	}

	/**
	 * @param pos the xPos to set
	 */
	public void setXPos(int pos) {
		xPos = pos;
	}

	/**
	 * @param pos the yPos to set
	 */
	public void setYPos(int pos) {
		yPos = pos;
	}

	/**
	 * @return a String representation of this component
	 */
	@Override
	public String toString() {
		return super.toString() + "[x=" + xPos + ",y=" + yPos + ",width="
		+ width + ",height=" + height + "]";
	}
	
	/**
	 * Converts this ALayoutComponent object to XML
	 * @param doc the document
	 * @return the element for this ALayoutComponent
	 */
	public abstract Element toXML(Document doc);

	/**
	 * Helper method for generating XML: Adds the unique ID, x, and y
	 * attributes, and adds properties for up, down, left, right, next, and
	 * previous.
	 * @param doc the document
	 * @param compElt the element of the component
	 */
	protected void addCommonAttributes(Document doc, Element compElt) {
		compElt.setAttribute("uid", uniqueID);
		compElt.setAttribute("x", Integer.toString(xPos));
		compElt.setAttribute("y", Integer.toString(yPos));
		if (up != null)
			XMLTools.addProperty(doc, compElt, "up", "String", up.getUID());
		if (down != null)
			XMLTools.addProperty(doc, compElt, "down", "String", down.getUID());
		if (left != null)
			XMLTools.addProperty(doc, compElt, "left", "String", left.getUID());
		if (right != null)
			XMLTools.addProperty(doc, compElt, "right", "String", right
					.getUID());
		if (next != null)
			XMLTools.addProperty(doc, compElt, "next", "String", next.getUID());
		if (previous != null)
			XMLTools.addProperty(doc, compElt, "previous", "String", previous
					.getUID());
	}

}
