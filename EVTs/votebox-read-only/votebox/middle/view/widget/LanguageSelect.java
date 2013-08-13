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

package votebox.middle.view.widget;

import votebox.middle.IncorrectTypeException;
import votebox.middle.Properties;
import votebox.middle.view.BallotBoxViewException;
import votebox.middle.view.IViewManager;

/**
 * This strategy defines the behavior for a toggle button group whose purpose is
 * to select the language that is being used. ToggleButtons who belong to this
 * group must define Properties.LANGUAGE. The select method will fail silently
 * if it runs into problems.
 * 
 * @author Kyle
 * 
 */
public class LanguageSelect extends AToggleButtonGroupStrategy {

    private IViewManager _viewManager;

    /**
     * This is the public constructor for LanguageSelect
     * 
     * @param viewManagerAdapter
     *            Use this viewmanager as a context to set the language in.
     */
    public LanguageSelect(IViewManager viewManagerAdapter) {
        _viewManager = viewManagerAdapter;
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonGroupStrategy#select(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void select(ToggleButton context) {
        try {
            _viewManager.setLanguage( context.getProperties().getString(
                Properties.LANGUAGE ) );
        }
        catch (IncorrectTypeException e) {
            throw new BallotBoxViewException(
                    "Problem while selecting a language.", e );
        }
        RadioButton.Singleton.select( context );
    }

    /**
     * @see votebox.middle.view.widget.AToggleButtonGroupStrategy#deselect(votebox.middle.view.widget.ToggleButton)
     */
    @Override
    public void deselect(ToggleButton context) {
    // NO-OP
    }

}
