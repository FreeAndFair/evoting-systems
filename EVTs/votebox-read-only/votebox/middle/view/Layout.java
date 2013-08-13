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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import votebox.middle.IBallotVars;
import votebox.middle.Properties;
import votebox.middle.ballot.IBallotLookupAdapter;
import votebox.middle.driver.IAdapter;
import votebox.middle.driver.UnknownUIDException;


/**
 * This class encapsulates the notion of "layout." A layout is essentially a
 * group of properties parsed from the layout xml file, and an ordered list of
 * RenderPages that can be drawn to the display.
 * 
 * @author Kyle
 * 
 */
public class Layout {

    /**
     * These are the pages that constitute the layout.
     */
    private List<RenderPage> _pages;

    /**
     * These are the properties for this layout that were parsed out of the
     * layout xml.
     */
    private Properties _properties;

    /**
     * This is a mapping from uid to the drawables which owns that uid.
     */
    private HashMap<String, LinkedList<IDrawable>> _uidMap;

    /**
     * This is the public constructor for Layout.
     * 
     * @param properties
     *            These are the properties for this layout that were parsed out
     *            of the layout xml.
     * @param pages
     *            These are the pages that constitute the layout.
     * @param drawables
     * 	          a map of UIDs to lists of the associated drawable elements.
     */
    public Layout(Properties properties, List<RenderPage> pages,
            HashMap<String, LinkedList<IDrawable>> drawables) {
        _properties = properties;
        _pages = pages;
        _uidMap = drawables;
        setChildren();
    }

    /**
     * Set the parent reference for all the children.
     */
    private void setChildren() {
        for (RenderPage rp : _pages)
            rp.setParent( this );
    }

    /**
     * This is the getter for _properties.
     * 
     * @return _properties.
     */
    public Properties getProperties() {
        return _properties;
    }

    /**
     * This is the getter for _pages
     * 
     * @return _pages
     */
    public List<RenderPage> getPages() {
        return _pages;
    }

    /**
     * Call this method to check if a UID is used for more than one drawable in
     * this layout.
     * 
     * @param uid
     *            Check for this UID
     * @return This method returns true if the given uid has more than one
     *         binding, or false if not.
     */
    public boolean isDuplicate(String uid) {
        return _uidMap.containsKey( uid ) && _uidMap.get( uid ).size() > 1;
    }

    /**
     * Look up the bound instances of a drawable by UID.
     * 
     * @param uid
     *            The drawable with this UID will be looked up
     * @return This method returns a list containing the drawable instances
     *         bound to a given UID, where lower orders indicies in the list
     *         denote more recently bound instances.
     * @throws UnknownUIDException
     *             This method throws if the given uid is not bound to any
     *             drawable.
     */
    public List<IDrawable> lookup(String uid) throws UnknownUIDException {
        if (_uidMap.containsKey( uid ))
            return _uidMap.get( uid );
        else
            throw new UnknownUIDException( uid );
    }

    /**
     * Lookup which page a particular drawable exists in.
     * 
     * @param uid
     *            The drawable with this UID will be looked up.
     * @return This method returns the page number that holds the drawable named
     *         by the given UID.
     * @throws UnknownUIDException
     *             This method throws if the UID doesn't exist in the layout.
     * @throws DuplicateUIDException
     *             This method throws if the given UID exists more than once in
     *             the layout.
     */
    public int lookupPage(String uid) throws UnknownUIDException,
            DuplicateUIDException {
        if (!_uidMap.containsKey( uid ))
            throw new UnknownUIDException( uid );

        if (isDuplicate( uid ))
            throw new DuplicateUIDException( uid );

        for (int lcv = 0; lcv < _pages.size(); lcv++)
            for (IDrawable d : _pages.get( lcv ).getChildren())
                if (d.getUniqueID().equals( uid ))
                    return lcv;

        throw new RuntimeException( "Control can never get here." );
    }

    /**
     * Call this method to draw a given page number to a given view. If the page
     * number given is out of range, this method will adhere to the nearest
     * index extrema.
     * 
     * @param pagenum
     *            This is the page number that wishes to be drawn.
     * @param view
     *            This is the view that the page wishes to be drawn to.
     */
    public void draw(int pagenum, IView view) {
        try {
            _pages.get( pagenum ).draw( view );
        }
        catch (IndexOutOfBoundsException e) {
            throw new BallotBoxViewException(
                    "You have attempted to draw a page which does not exist:"
                            + e.getMessage(), e );
        }
    }

    public void initFromViewManager(int pagenum, IViewManager vmadapter,
            IBallotLookupAdapter lookupadapter, IAdapter ballotadapter,
            IViewFactory viewadapter, IBallotVars ballotvars) {
        _pages.get( pagenum ).initFromViewManager( vmadapter, lookupadapter,
            ballotadapter, viewadapter, ballotvars );

    }

    public void initFromViewManager(ViewManager manager,
            IBallotLookupAdapter lookupAdapter, IAdapter ballotAdapter,
            IViewFactory factory, IBallotVars ballotvars) {
        for (RenderPage rp : _pages)
            rp.initFromViewManager( manager, lookupAdapter, ballotAdapter,
                factory, ballotvars );
    }
}
