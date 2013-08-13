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

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import javax.imageio.ImageIO;
import javax.swing.JPanel;

import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import preptool.model.ballot.ACard;
import preptool.model.ballot.Ballot;
import preptool.model.language.Language;
import preptool.model.layout.ALayoutComponent;
import preptool.model.layout.Background;
import preptool.model.layout.Button;
import preptool.model.layout.ILayoutComponentVisitor;
import preptool.model.layout.Label;
import preptool.model.layout.Layout;
import preptool.model.layout.Page;
import preptool.model.layout.ReviewButton;
import preptool.model.layout.ReviewLabel;
import preptool.model.layout.ToggleButton;
import preptool.model.layout.ToggleButtonGroup;
import preptool.view.ProgressInfo;


/**
 * ALayoutManager is a more useful abstraction of the LayoutManager, providing
 * methods for different types of pages, and also implementing a card visitor to
 * layout the different types of cards.
 * @author cshaw
 */
public abstract class ALayoutManager implements ILayoutManager {

	/** 
	 * Use a thread pool when exporting images to speed up ballot export on
	 * multi-core machines. Experimental. [dsandler]
	 */
	public static final Boolean USE_THREADS = true;
	
	/**
     * Creates a Layout using the information from the given Ballot.
     * @param ballot the ballot
     * @return the layout
     */
    public abstract Layout makeLayout(Ballot ballot);

    /**
     * Executes this as a visitor to get a JPanel for the card's type
     * @param card the card
     * @return a JPanel with all elements laid out on it
     */
    public abstract ArrayList<JPanel> makeCardPage(ACard card);

    /**
     * Makes a review page that shows all of the cards on the screen and allows
     * the user to go back and change his response.
     * @param ballot the ballot
     * @param pageTargets mapping of races to review pages
     * @return the review page
     */
    protected abstract ArrayList<Page> makeReviewPage(Ballot ballot,
            HashMap<Integer, Integer> pageTargets);

    /**
     * Makes an introductory page with instructions on how to use VoteBox.
     * @return the instructions page
     */
    protected abstract Page makeInstructionsPage(boolean hadLanguageSelect);

    /**
     * Makes a cast ballot page that asks the user for confirmation.
     * @return the cast ballot page
     */
    protected abstract Page makeCastPage();

    /**
     * Makes a language selection page that gives the user an option of
     * different languages
     * @param languages a list of the languages available
     */
    protected abstract Page makeLanguageSelectPage(ArrayList<Language> languages);
    
    /**
     * Makes a special page that is shown when an override-cancel message
     * is received, and asks for confirmation
     */
    protected abstract Page makeOverrideCancelPage();
    
    /**
     * Makes a special page that is shown when an override-cast message
     * is received, and asks for confirmation
     */
    protected abstract Page makeOverrideCastPage();

    /**
     * Makes a success page that informs the user that the ballot was
     * successfully cast.
     * @return the success page
     */
    protected abstract Page makeSuccessPage();
    
    /**
     * Makes a challenge page that asks the user whether he wishes to
     * challenge the VoteBox or cast his ballot.
     * @return the challenge page
     */
    protected abstract Page makeChallengePage();
    
    /**
     * Makes a response page that reveals the random number used to generate
     * the ballot to the user, who can then use it to verify his ballot.
     * @return the response page
     */
    protected abstract Page makeResponsePage();

    /**
     * Returns a size visitor that determines the size of a component specific
     * to this layout configuration
     * @return the visitor
     */
    public abstract ILayoutComponentVisitor<Object, Dimension> getSizeVisitor();

    /**
     * Returns an image visitor that renders an image of a component specific to
     * this layout configuration
     * @return the visitor
     */
    public abstract ILayoutComponentVisitor<Boolean, BufferedImage> getImageVisitor();

    /**
     * The next unique ID to assign
     */
    private int nextUID = 1;

    /**
     * Returns the next unique ID with an L in front (for Layout), and
     * increments the counter
     * @return the unique ID
     */
    public String getNextLayoutUID() {
        return "L" + nextUID++;
    }

    /**
     * Returns the next unique ID with a B in front (for Ballot), and increments
     * the counter
     * @return the unique ID
     */
    public String getNextBallotUID() {
        return "B" + nextUID++;
    }

    /**
     * Sets the unique IDs of the entire ballot
     * @param ballot the ballot
     */
    public final void assignUIDsToBallot(Ballot ballot) {
        ballot.assignUIDsToBallot(this);
    }

    /**
     * Renders all images in a Layout to disk, ignoring duplicates.
     * @param layout the layout holding images
     * @param location path to output the images to
     * @param progressInfo used to indicate the status of the rendering
     */
    public void renderAllImagesToDisk(final Layout layout, final String location,
            ProgressInfo progressInfo) {
        final HashSet<String> uids = new HashSet<String>();
        final String langShortName = getLanguage().getShortName();
        File path = new File(location);
        if (!path.exists()) path.mkdirs();
        final ILayoutComponentVisitor<Object, Void> renderVisitor = new ILayoutComponentVisitor<Object, Void>() {
            public Void forBackground(Background bg, Object... param) {
                if (!uids.contains(bg.getUID())) {
                    try {
                        BufferedImage img = bg.execute(getImageVisitor());
                        ImageIO
                                .write(img, "png", new File(location
                                        + bg.getUID() + "_1_" + langShortName
                                        + ".png"));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    uids.add(bg.getUID());
                }
                return null;
            }

            public Void forButton(Button b, Object... param) {
                if (!uids.contains(b.getUID())) {
                    try {
                        BufferedImage img = b.execute(getImageVisitor());
                        ImageIO.write(img, "png", new File(location
                                + b.getUID() + "_1_" + langShortName + ".png"));
                        ImageIO.write(img, "png", new File(location
                                + b.getUID() + "_focused_1_" + langShortName
                                + ".png"));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    uids.add(b.getUID());
                }
                return null;
            }

            public Void forLabel(Label l, Object... param) {
                if (!uids.contains(l.getUID())) {
                    try {
                        BufferedImage img = l.execute(getImageVisitor());
                        ImageIO.write(img, "png", new File(location
                                + l.getUID() + "_1_" + langShortName + ".png"));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    uids.add(l.getUID());
                }
                return null;
            }

            public Void forReviewButton(ReviewButton rb, Object... param) {
                String uid = rb.getUID();
                if (!uids.contains(uid)) {
                    try {
                        BufferedImage img = rb.execute(getImageVisitor());
                        ImageIO.write(img, "png", new File(location + uid
                                + "_1_" + langShortName + ".png"));
                        ImageIO.write(img, "png", new File(location + uid
                                + "_focused_1_" + langShortName + ".png"));
                        
                        /**
                         * Renders the VVPAT equivalent of the review button.
                         */
                        BufferedImage smaller = getImageVisitor().forVVPATReviewButton(rb);
                        File file = new File(location);
                        file = new File(file, "vvpat");
                        if(!file.exists())
                        	file.mkdirs();
                        
                        file = new File(file, uid+"_"+langShortName+".png");
                        
                        ImageIO.write(smaller, "png", file);
                        
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    uids.add(uid);
                }
                return null;
            }

            public Void forReviewLabel(ReviewLabel rl, Object... param) {
                if (!uids.contains(rl.getUID())) {
                    try {
                        BufferedImage img = rl.execute(getImageVisitor());
                        ImageIO
                                .write(img, "png", new File(location
                                        + rl.getUID() + "_1_" + langShortName
                                        + ".png"));
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    uids.add(rl.getUID());
                }
                return null;
            }

            public Void forToggleButton(ToggleButton tb, Object... param) {
                if (!uids.contains(tb.getUID())) {
                    try {
                        BufferedImage img = tb
                                .execute(getImageVisitor(), false);
                        ImageIO
                                .write(img, "png", new File(location
                                        + tb.getUID() + "_1_" + langShortName
                                        + ".png"));
                        ImageIO.write(img, "png", new File(location
                                + tb.getUID() + "_focused_1_" + langShortName
                                + ".png"));
                        img = tb.execute(getImageVisitor(), true);
                        ImageIO.write(img, "png", new File(location
                                + tb.getUID() + "_selected_1_" + langShortName
                                + ".png"));
                        ImageIO.write(img, "png", new File(location
                                + tb.getUID() + "_focusedSelected_1_"
                                + langShortName + ".png"));
                        ReviewButton review = new ReviewButton(tb.getUID()
                                + "_review", tb.getBothLines(), "GoToPage",
                                getSizeVisitor());
//                      Added party info for ZH study here. [dsandler]
						review.setAuxText(tb.getParty());
                        review.setBoxed(false);
                        review.setWidth(100);
                        review.execute(this, param);
                    } catch (IOException e) {
                        throw new RuntimeException(e);
                    }
                    uids.add(tb.getUID());
                }
                return null;
            }

            public Void forToggleButtonGroup(ToggleButtonGroup tbg,
                    Object... param) {
                for (ToggleButton tb : tbg.getButtons())
                    tb.execute(this);
                return null;
            }

			public Void forVVPATReviewButton(ReviewButton rb, Object... param) {
				throw new RuntimeException("VVPAT Review Button cannot be generated at this time.");
			}
        };
        final int totalIDs = nextUID;
        int graphicsDrawn = 0;

		// Multithreaded rendering to better take advantage of multi-core
		// computers. [dsandler]

		int nProc = java.lang.Runtime.getRuntime().availableProcessors();
		ExecutorService exc = Executors.newFixedThreadPool(
			(USE_THREADS && (nProc > 1))
				? (nProc + 1) 
				: 1
		);

		final ProgressInfo _progressInfo = progressInfo;

        for (Page p : layout.getPages()) {
            for (ALayoutComponent c : p.getComponents()) {
				graphicsDrawn++;
				final int graphicsDrawnF = graphicsDrawn;
				final ALayoutComponent _c = c;
				exc.execute(new Runnable() {
					public void run() {
						if (_progressInfo.isCancelled()) return;
						if (!uids.contains(_c.getUID())) {
							_progressInfo.setProgress("Rendering Images", 100
									* graphicsDrawnF / totalIDs);
							_c.execute(renderVisitor);
						}
					}
				});
            }
        }
        
        exc.execute(new Runnable(){
        	public void run(){
        		File file = new File(location);
                file = new File(file, "vvpat");
                if(!file.exists())
                	file.mkdirs();
                
                file = new File(file, "spoil.png");
                
                BufferedImage spoil = RenderingUtils.renderLabel("***Voter Rejected Ballot***", "", "", 12, 1024, Color.black, false, false, false);
                
                try {
					ImageIO.write(spoil, "png", file);
				} catch (IOException e) {
					System.out.println("Spoiled image creation failed!");
					e.printStackTrace();
				}
        	}
        });
        
        exc.execute(new Runnable(){
        	public void run(){
        		File file = new File(location);
                file = new File(file, "vvpat");
                if(!file.exists())
                	file.mkdirs();
                
                file = new File(file, "accept.png");
                
                BufferedImage subSpoil = RenderingUtils.renderLabel("***Voter Accepted Ballot***", "", "", 12, 1024, Color.black, false, false, false);
                
                BufferedImage spoil = new BufferedImage(subSpoil.getWidth(), subSpoil.getHeight(), BufferedImage.TYPE_BYTE_BINARY);
                Graphics g = spoil.getGraphics();
                g.setColor(Color.white);
                g.fillRect(0, 0, spoil.getWidth(), spoil.getHeight());
                g.drawImage(subSpoil, 0, 0, null);
                
                try {
					ImageIO.write(spoil, "png", file);
				} catch (IOException e) {
					System.out.println("Accepted ballot creation failed!");
					e.printStackTrace();
				}
        	}
        });

		exc.shutdown();
		while (true) {
			try {
				exc.awaitTermination(120L, TimeUnit.SECONDS);
				break;
			} catch (java.lang.InterruptedException e) {
				// pass
			}
		}
    }

    /**
     * @return the language
     */
    public abstract Language getLanguage();

    /**
     * An interface for a card layout object. Cards can add information to the
     * card layout via these methods, and the specific implementation (usually
     * tied to the LayoutManager) knows what to do with it. Then the
     * makeIntoPanels method can be called and a list of JPanels is returned
     * with all information laid out properly.
     * @author cshaw
     */
    public interface ICardLayout {

        /**
         * Sets the title of this card
         * @param title the title
         */
        public void setTitle(String title);

        /**
         * Sets a description on this card
         * @param description the description
         */
        public void setDescription(String description);

        /**
         * Adds a candidate to this card layout
         * @param uid the UID of the candidate
         * @param name the name of the candidate
         */
        public void addCandidate(String uid, String name);

        /**
         * Adds a candidate to this card layout
         * @param uid the UID of the candidate
         * @param name the name of the candidate
         * @param party the candidate's party
         */
        public void addCandidate(String uid, String name, String party);

        /**
         * Adds a candidate to this card layout
         * @param uid the UID of the candidate
         * @param name the name of the candidate
         * @param name2 the name of the running mate
         * @param party the candidate's party
         */
        public void addCandidate(String uid, String name, String name2,
                String party);

        /**
         * Returns this card layout as a list of laid out JPanels
         */
        public ArrayList<JPanel> makeIntoPanels();

    }
}
