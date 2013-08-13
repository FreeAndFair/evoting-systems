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

import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.lang.ref.SoftReference;

import javax.imageio.ImageIO;

/**
 * This is a wrapper for the AWT Image class, BufferedImage.
 * 
 * @author kyle
 * 
 */
public class AWTImage implements IViewImage {

    private final String _filename;
    private SoftReference<BufferedImage> _bufferedImage;

    /**
     * Construct a new AWT Image.
     * 
     * @param filename
     *            Construct an image that loads its bytes from this path.
     */
    public AWTImage(String filename) {
        _bufferedImage = new SoftReference<BufferedImage>( null );
        _filename = filename;
    }

    /**
     * @see votebox.middle.view.IViewImage#getImage()
     */
    public BufferedImage getImage() {
        if (_bufferedImage.get() == null)
            try {
                _bufferedImage = new SoftReference<BufferedImage>( ImageIO
                        .read( new File( _filename ) ) );

            }
            catch (IOException e) {
                throw new BallotBoxViewException( "The file " + _filename
                        + " could not be loaded to represent an image", e );
            }

        return _bufferedImage.get();
    }

    /**
     * @see votebox.middle.view.IViewImage#getHeight()
     */
    public int getHeight() {
        return getImage().getHeight();
    }

    /**
     * @see votebox.middle.view.IViewImage#getWidth()
     */
    public int getWidth() {
        return getImage().getWidth();
    }
}
