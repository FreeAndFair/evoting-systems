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

import votebox.middle.IncorrectTypeException;
import votebox.middle.ballot.IBallotLookupAdapter;

/**
 * Other classes that make use of the ViewManager should program to this
 * abstraction, and not to the concrete ViewManager class. This allows for much
 * easier testing.
 * 
 * @author Kyle
 * 
 */
public interface IViewManager {

    /**
     * Flip to the next page.
     */
    void nextPage();

    /**
     * Flip to the previous page.
     */
    void previousPage();

    /**
     * Flip to a particular page.
     * 
     * @param pagenum
     *            Flip to this page.
     */
    void drawPage(int pagenum);
    
    /**
     * Commit the ballot.
     */
    void commitBallot();

    /**
     * Cast the ballot.
     */
    void castBallot();
    
    /**
     * Cast the ballot.
     */
    void challenge() throws IncorrectTypeException;
    
    /**
     * Fired when the override-cancel operation is confirmed on the booth.
     */
    public void overrideCancelConfirm();
    
    /**
     * Fired when the override-cancel operation is denied from the booth.
     */
    public void overrideCancelDeny();
    
    /**
     * Fired when the override-cast operation is confirmed on the booth.
     */
    public void overrideCastConfirm();
    
    /**
     * Fired when the override-cast operation is confirmed on the booth.
     */
    public void overrideCastDeny();

    /**
     * Set the language being displayed in the view.
     * 
     * @param language
     *            Set the language to this.
     */
    void setLanguage(String language);

    /**
     * Set the size being displayed in the view.
     * 
     * @param size
     *            Set the size to this.
     */
    void setSize(int size);

    /**
     * Get the current size.
     * 
     * @return This method returns the current size of images that the view
     *         manager is asking to have displayed.
     */
    int getSize();

    /**
     * Get the current language.
     * 
     * @return This method returns the current language of images that the view
     *         manager is asking to have displayed.
     */
    String getLanguage();
    
    /**
     * Gets the IBallotLookupAdapter for this IViewManager.
     * @return The IBallotLookupAdapter.
     */
    IBallotLookupAdapter getBallotLookupAdapter();
}
