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

import java.util.ArrayList;


import org.w3c.dom.Document;
import org.w3c.dom.Element;

import preptool.model.XMLTools;

/**
 * A Page represents what a user would see on the screen at any point during
 * voting. Each Page contains a list of ALayoutComponents, which keep track of
 * their size and location, and can be rendered on the screen.
 * @author cshaw
 */
public class Page {

	/**
	 * Indiciates whether or not a page is a review screen.
	 */
	private boolean isReviewPage = false;
	
	/**
	 * The array of components on this Page
	 */
	private ArrayList<ALayoutComponent> components;

	/**
	 * The title component on this Page
	 */
	private ALayoutComponent title;
	
	/**
	 * Unique ID of the background label (if any)
	 */
	private String backgroundLabel = "";

	/**
	 * Constructs a blank page with an empty list of components.
	 */
	public Page() {
		components = new ArrayList<ALayoutComponent>();
	}

	/**
	 * @return the backgroundLabel
	 */
	public String getBackgroundLabel() {
		return backgroundLabel;
	}

	
	
	/**
	 * @return the list of components
	 */
	public ArrayList<ALayoutComponent> getComponents() {
		return components;
	}

	/**
	 * @param backgroundLabel the backgroundLabel to set
	 */
	public void setBackgroundLabel(String backgroundLabel) {
		this.backgroundLabel = backgroundLabel;
	}

	/**
	 * @return a String for this Page
	 */
	@Override
	public String toString() {
		return super.toString() + "[ " + components + "]";
	}

	/**
	 * Converts this Page object to XML
	 * @param doc the document
	 * @return the element for this Page
	 */
	public Element toXML(Document doc) {
		Element pageElt = doc.createElement("Page");
		if (!backgroundLabel.equals(""))
			XMLTools.addProperty(doc, pageElt, "BackgroundLabel", "String",
					backgroundLabel);
		for (ALayoutComponent comp : components) {
			Element compElt = comp.toXML(doc);
			pageElt.appendChild(compElt);
		}
		
		if(isReviewPage)
			XMLTools.addProperty(doc, pageElt, "IsReviewPage", "String", "yes");
		
		return pageElt;
	}

	public void markAsReviewPage() {
		isReviewPage = true;
	}
	
	public void setTitle(ALayoutComponent title){
		this.title = title;
	}
	
	public ALayoutComponent getTitle(){
		return title;
	}
}
