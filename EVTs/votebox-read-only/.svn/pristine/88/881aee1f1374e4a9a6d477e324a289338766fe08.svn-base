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

import java.awt.Color;
import java.awt.Dimension;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

/**
 * A Label is a component that consists of some text that has no action when it
 * is clicked.
 * @author cshaw
 */
public class Label extends ALayoutComponent {

	/**
	 * The text of this label
	 */
	private String text;

	/**
	 * An additional description for this label (used in propositions)
	 */
	private String description = "";
	
	/**
	 * An italicized string below the main label (used for multi-page races)
	 */
	private String instructions = "";

	/**
	 * Whether this label is centered
	 */
	private boolean centered;

	/**
	 * Whether this label is bold
	 */
	private boolean bold;

	/**
	 * Whether this label has an increased font size
	 */
	private boolean increasedFontSize;

	/**
	 * Whether this label is surrounded by a box
	 */
	private boolean boxed;

	/**
	 * The color to render this label's text in
	 */
	private Color color = Color.BLACK;

	/**
	 * Constructs a new label with given unique ID and text
	 * @param uid the unique ID
	 * @param t the text
	 */
	public Label(String uid, String t) {
		super(uid);
		text = t;
	}

	/**
	 * Constructs a new Label with given unique ID, text, and size visitor,
	 * which determines and sets the size
	 * @param uid the unique ID
	 * @param t the text
	 * @param sizeVisitor the size visitor
	 */
	public Label(String uid, String t,
			ILayoutComponentVisitor<Object,Dimension> sizeVisitor) {
		this(uid, t);
		setSize(execute(sizeVisitor));
	}

	/**
	 * Constructs a new Label with given unique ID, text, and width and height.
	 * @param uid the unique ID
	 * @param t the text
	 * @param width the width
	 * @param height the height
	 */
	public Label(String uid, String t, int width, int height) {
		this(uid, t);
		this.width = width;
		this.height = height;
	}

	/**
	 * Calls the forLabel method in visitor
	 * @param visitor the visitor
	 * @param param parameters
	 * @return the result of the visitor
	 */
	@Override
	public <P,R> R execute(ILayoutComponentVisitor<P,R> visitor, P... param) {
		return visitor.forLabel(this, param);
	}

	/**
	 * @return the color
	 */
	public Color getColor() {
		return color;
	}

	/**
	 * @return the description
	 */
	public String getDescription() {
		return description;
	}

	/**
	 * @return the instructions
	 */
	public String getInstructions() {
		return instructions;
	}

	/**
	 * @return the text of this label
	 */
	public String getText() {
		return text;
	}

	/**
	 * @return if the label is bold
	 */
	public boolean isBold() {
		return bold;
	}

	/**
	 * @return if the label is boxed
	 */
	public boolean isBoxed() {
		return boxed;
	}

	/**
	 * @return if the label is centered
	 */
	public boolean isCentered() {
		return centered;
	}

	/**
	 * @return if the label has increasedFontSize
	 */
	public boolean isIncreasedFontSize() {
		return increasedFontSize;
	}

	/**
	 * @param bold the bold to set
	 */
	public void setBold(boolean bold) {
		this.bold = bold;
	}

	/**
	 * @param boxed the boxed to set
	 */
	public void setBoxed(boolean boxed) {
		this.boxed = boxed;
	}

	/**
	 * @param centered the centered to set
	 */
	public void setCentered(boolean centered) {
		this.centered = centered;
	}

	/**
	 * @param color the color to set
	 */
	public void setColor(Color color) {
		this.color = color;
	}

	/**
	 * @param description the description to set
	 */
	public void setDescription(String description) {
		this.description = description;
	}

	/**
	 * @param increasedFontSize the increasedFontSize to set
	 */
	public void setIncreasedFontSize(boolean increasedFontSize) {
		this.increasedFontSize = increasedFontSize;
	}

	/**
	 * @param instructions the instructions to set
	 */
	public void setInstructions(String instructions) {
		this.instructions = instructions;
	}

	/**
	 * @return a String represnetation of this label
	 */
	@Override
	public String toString() {
		return "Label[text=" + text + ",x=" + xPos + ",y=" + yPos + ",width="
				+ width + ",height=" + height + "]";
	}

	/**
	 * Converts this Label object to XML
	 * @param doc the document
	 * @return the element for this Label
	 */
	@Override
	public Element toXML(Document doc) {
		Element labelElt = doc.createElement("Label");
		addCommonAttributes(doc, labelElt);
		return labelElt;
	}

}
