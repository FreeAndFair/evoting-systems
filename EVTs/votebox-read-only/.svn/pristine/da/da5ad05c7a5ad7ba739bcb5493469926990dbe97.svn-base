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

import java.awt.image.BufferedImage;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

/**
 * A component that represents the background image of a page
 * @author cshaw
 */
public class Background extends ALayoutComponent {

	/**
	 * The image
	 */
	private BufferedImage image;

	/**
	 * Constructs a new Background with given unique ID and image
	 * @param uid the unique ID
	 * @param img the image
	 */
	public Background(String uid, BufferedImage img) {
		super(uid);
		image = img;
		width = img.getWidth();
		height = img.getHeight();
	}

	/**
	 * Calls the forBackground method in visitor
	 * @param visitor the visitor
	 * @param param list of parameters to pass to the appropriate visitor method
	 * @return the result of the visitor
	 */
	@Override
	public <P,R> R execute(ILayoutComponentVisitor<P,R> visitor, P... param) {
		return visitor.forBackground(this, param);
	}

	/**
	 * @return the image
	 */
	public BufferedImage getImage() {
		return image;
	}

	/**
	 * @param image the image to set
	 */
	public void setImage(BufferedImage image) {
		this.image = image;
	}

	/**
	 * Converts this Background object to XML (same as a Label)
	 * @param doc the document
	 * @return the element for this Background
	 */
	@Override
	public Element toXML(Document doc) {
		Element labelElt = doc.createElement("Label");
		addCommonAttributes(doc, labelElt);
		return labelElt;
	}

}
