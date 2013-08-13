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

import votebox.middle.IBallotVars;
import votebox.middle.Properties;
import votebox.middle.ballot.IBallotLookupAdapter;
import votebox.middle.driver.IAdapter;
import votebox.middle.view.IDrawable;
import votebox.middle.view.IViewFactory;
import votebox.middle.view.IViewImage;
import votebox.middle.view.IViewManager;
import votebox.middle.view.MeaninglessMethodException;
import votebox.middle.view.RenderPage;

/**
 * This is the simplest implementation of an IDrawable. Labels are simply window
 * decoration. Labels cannot be interacted with by the voter.
 */

public class Label implements IDrawable {

    private final String _uniqueID;
    private final Properties _properties;

    private RenderPage _parent;
    private int _x;
    private int _y;

    private IViewImage _image;
    private IViewImage _reviewImage;
    
    protected IViewFactory _factory;
    protected IViewManager _viewManager;
    protected IBallotVars _vars;
    protected IBallotLookupAdapter _ballot;

    /**
     * This is the public constructor for Label.
     * 
     * @param uid
     *            This is the drawable's UID.
     * @param properties
     *            These are the properties that were defined for this label.
     */
    public Label(String uid, Properties properties) {
        _uniqueID = uid;
        _properties = properties;
    }

    /**
     * Call this method to set the parent of this label.
     */
    public void setParent(RenderPage page) {
        _parent = page;
    }

    /**
     * Call this method to get the parent of this label.
     * 
     * @return This method returns the parent of this label.
     */
    protected RenderPage getParent() {
        return _parent;
    }

    /**
     * @see votebox.middle.view.IDrawable#getImage()
     */
    public IViewImage getImage() {
        if (_image == null) {
            if (_uniqueID.equals( "reviewtitle" ))
                _image = _factory.makeImage( imagePath( _vars, _uniqueID
                        + Integer.toString( _ballot.numSelections() ),
                    _viewManager.getSize(), _viewManager.getLanguage() ) );
            else
                _image = _factory.makeImage( imagePath( _vars, _uniqueID,
                    _viewManager.getSize(), _viewManager.getLanguage() ) );
        }

        return _image;
    }

    /**
     * @see votebox.middle.view.IDrawable#getImage()
     */
    public IViewImage getReviewImage() {
        if (_reviewImage == null) {
            _reviewImage = _factory.makeImage( imagePath( _vars, _uniqueID
                    + "_review", _viewManager.getSize(), _viewManager
                    .getLanguage() ) );
        }
        return _reviewImage;
    }

    /**
     * This is the getter for _unqiueID.
     * 
     * @return _uniqueID
     */
    public String getUniqueID() {
        return _uniqueID;
    }

    /**
     * This is the getter for _properties.
     * 
     * @return _properties
     */
    public Properties getProperties() {
        return _properties;
    }

    /**
     * Call this method to get the x-coordinate at which this drawable should be
     * drawn.
     * 
     * @return The x-coordinate at which this drawable should be drawn.
     */
    public int getX() {
        return _x;
    }

    /**
     * Call this method to set the x-coordinate at which this drawable should be
     * drawn.
     * 
     * @param x
     *            This int will be set as the x-coordinate at which this
     *            drawable should be drawn.
     */
    public void setX(int x) {
        _x = x;
    }

    /**
     * Call this method to get the y-coordinate at which this drawable should be
     * drawn.
     * 
     * @return The y-coordinate at which this drawable should be drawn.
     */
    public int getY() {
        return _y;
    }

    /**
     * Call this method to set the y-coordinate at which this drawable should be
     * drawn.
     * 
     * @param y
     *            This int will be set as the y-coordinate at which this
     *            drawable should be drawn.
     */
    public void setY(int y) {
        _y = y;
    }

    public ToggleButtonGroup getGroup() throws MeaninglessMethodException {
        throw new MeaninglessMethodException( "Labels do not define a group." );
    }

    /**
     * The location on disk that the image wrappers will use to do the loading
     * of the images depends on the uid, size, language. There is *one* special
     * case here: if the uid is "reviewtitle", append the number of selections
     * the ballot thinks have been made onto the uid. Therefore, if there have
     * been 4 selections made in the ballot, the uid of this element should be
     * interpreted as "reviewtitle4". Because we need a reference to the ballot
     * lookup adapter in order to check the number of selections, we must insert
     * this behavior here.
     * 
     */
    public void initFromViewmanager(IViewManager viewManagerAdapter,
            IBallotLookupAdapter ballotLookupAdapter, IAdapter ballotAdapter,
            IViewFactory factory, IBallotVars ballotVars) {
        _factory = factory;
        _vars = ballotVars;
        _ballot = ballotLookupAdapter;
        _viewManager = viewManagerAdapter;
    }

    /**
     * Construct the full path to an image given several paramters.
     * 
     * @param vars
     *            This is the vars object that has the ballot bath.
     * @param uid
     *            This is the image's unique id
     * @param size
     *            This is the image's size index
     * @param lang
     *            This is the image's language abbreviation.
     * @return This method returns the path to the image.
     */
    protected String imagePath(IBallotVars vars, String uid, int size,
            String lang) {
        return vars.getBallotPath() + "/media/" + uid + "_" + size + "_" + lang
                + ".png";
    }

    /**
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return _uniqueID;
    }
}
