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
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.font.FontRenderContext;
import java.awt.geom.Rectangle2D;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import javax.swing.JFrame;
import javax.swing.JPanel;

import preptool.model.ballot.ACard;
import preptool.model.ballot.Ballot;
import preptool.model.language.Language;
import preptool.model.language.LiteralStrings;
import preptool.model.layout.Background;
import preptool.model.layout.Button;
import preptool.model.layout.ILayoutComponentVisitor;
import preptool.model.layout.Label;
import preptool.model.layout.LanguageButton;
import preptool.model.layout.Layout;
import preptool.model.layout.Page;
import preptool.model.layout.ReviewButton;
import preptool.model.layout.ReviewLabel;
import preptool.model.layout.ToggleButton;
import preptool.model.layout.ToggleButtonGroup;


/**
 * PsychLayoutManager is a concrete implementation of a LayoutManager, as
 * specified by the Psychology department.<br>
 * See the wiki for more details about this layout
 * @author cshaw, ttorous, derrley
 */
public class PsychLayoutManager extends ALayoutManager {

    /**
     * Constant used to indicate how wide the text boxes describing a 
     * race are to be drawn.
     */
    private static final int RACE_DESCRIPTION_WIDTH = 600;

    /**
     * Width of each candidate or contest on the VVPAT (RenderButton).
     */
    private static final int VVPAT_CAND_WIDTH = 239;
    private static final int VVPAT_FONT_SIZE_MULTIPLE = 7;
    
	/**
	 * Width of each candidate or contest on the review screen (RenderButton).
	 */
	private static final int REVIEW_SCREEN_RACE_WIDTH = 200;
	private static final int REVIEW_SCREEN_CAND_WIDTH = 330;
	private static final Boolean REVIEW_SCREEN_SHOW_PARTY = true;
	private static final Boolean REVIEW_SCREEN_PARENTHESIZE_PARTY = true;
	private static final int REVIEW_SCREEN_NUM_COLUMNS = 1;
	private static int CARDS_PER_REVIEW_PAGE = 10;
	
	private static boolean USE_COMMIT_CHALLENGE_MODEL = true;

    /**
     * Constant for the width of the language selection page box.
     */
    private static final int LANG_SELECT_WIDTH = 500;


    public class PsychCardLayout implements ICardLayout {

        private String titleText = "";

        private String descriptionText = "";

        private ArrayList<ToggleButton> candidates;

        public PsychCardLayout() {
            candidates = new ArrayList<ToggleButton>();
        }

        public void addCandidate(String uid, String name) {
            ToggleButton tb = new ToggleButton(uid, name);
            candidates.add(tb);
        }

        public void addCandidate(String uid, String name, String party) {
            ToggleButton tb = new ToggleButton(uid, name);
            tb.setParty(party);
            candidates.add(tb);
        }

        public void addCandidate(String uid, String name, String name2,
                String party) {
            ToggleButton tb = new ToggleButton(uid, name);
            tb.setSecondLine(name2);
            tb.setParty(party);
            candidates.add(tb);
        }

        public ArrayList<JPanel> makeIntoPanels() {
            int cnt = 0;
            ArrayList<JPanel> panels = new ArrayList<JPanel>();
            while (cnt < candidates.size()) {
                JPanel east = new JPanel();
                east.setLayout(new GridBagLayout());
                GridBagConstraints eastConstraints = new GridBagConstraints();

                eastConstraints.anchor = GridBagConstraints.SOUTH;
                eastConstraints.fill = GridBagConstraints.VERTICAL;
                int ycoord = 0; // the ycoordinate of where to add in gridbag
                eastConstraints.gridy = ycoord;
                eastConstraints.gridx = 0;

                ycoord++;
                Label title = new Label(getNextLayoutUID(), titleText);
                title.setDescription(descriptionText);
                title.setWidth(RACE_DESCRIPTION_WIDTH); 
                title.setBoxed(true);
                title.setCentered(true);
                if (candidates.size() > MAX_CANDIDATES)
                    title.setInstructions("("
                            + LiteralStrings.Singleton.get("PAGE", language)
                            + " "
                            + (cnt / MAX_CANDIDATES + 1)
                            + " "
                            + LiteralStrings.Singleton.get("OF", language)
                            + " "
                            + (int) Math.ceil((double) candidates.size()
                                    / MAX_CANDIDATES) + ")");
                title.setSize(title.execute(sizeVisitor));

                Spacer PTitle = new Spacer(title, east);
                east.add(PTitle, eastConstraints);

                ToggleButtonGroup tbg = new ToggleButtonGroup("Race");
                for (int i = 0; i < MAX_CANDIDATES && cnt < candidates.size(); ++i, ++cnt) {
                    ToggleButton button = candidates.get(cnt);
                    button.setWidth(RACE_DESCRIPTION_WIDTH);
                    button.setIncreasedFontSize(true);
                    button.setSize(button.execute(sizeVisitor));
                    eastConstraints.gridy = ycoord++;
                    eastConstraints.gridx = 0;
                    Spacer PDrawable = new Spacer(button, east);
                    east.add(PDrawable, eastConstraints);
                    tbg.getButtons().add(button);
                }
                east.add(new Spacer(tbg, east));

                panels.add(east);
            }
            return panels;
        }

        public void setDescription(String description) {
            this.descriptionText = description;
        }

        public void setTitle(String title) {
            this.titleText = title;
        }

    }

    /**
     * PsychLayoutPanel is a subclass of JFrame and is used to temporarily hold
     * layout components so that GridBagLayout can be used to get the locations
     * of all of the components.
     * @author cshaw
     */
    public class PsychLayoutPanel extends JFrame {

        private static final long serialVersionUID = 1L;

        /**
         * North panel (for the title)
         */
        public JPanel north;

        /**
         * South panel (for the navigation buttons)
         */
        public JPanel south;

        /**
         * East panel (for the main content of the page)
         */
        public JPanel east;

        /**
         * West panel (for the sidebar - current step)
         */
        public JPanel west;

        /**
         * Constructs a new PsychLayoutPanel. Initializes the frame, and the
         * four internal panes.
         */
        PsychLayoutPanel() {
            // Compute size of window
            int width = WINDOW_WIDTH;
            int height = WINDOW_HEIGHT;
            JFrame testFrame = new JFrame();
            testFrame.setSize(width, height);
            testFrame.pack();
            Insets insets = testFrame.getInsets();
            int insetwidth = insets.left + insets.right;
            int insetheight = insets.top + insets.bottom;
            height = height + insetheight - 2;
            width = width + insetwidth - 2;
            setSize(width, height);

            // Initialize frame
            pack();
            setPreferredSize(new Dimension(width, height));
            setMinimumSize(new Dimension(width, height));
            setResizable(false);
            setLayout(new GridBagLayout());
            north = new JPanel();
            south = new JPanel();
            west = new JPanel();
            east = new JPanel();

            // Initialize west pane
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.fill = GridBagConstraints.BOTH;
            constraints.gridx = 0;
            constraints.gridy = 0;
            constraints.gridheight = 3;
            constraints.gridwidth = 1;
            constraints.weighty = 1;
            constraints.weightx = 0; // .25
            west.setBackground(new Color(48, 149, 242));
            add(west, constraints);
            west.setLayout(new GridBagLayout());

            // Initialize north pane
            constraints.gridx = 1;
            constraints.gridy = 0;
            constraints.gridheight = 1;
            constraints.gridwidth = 1;
            constraints.weighty = 0;
            constraints.weightx = 0;
            north.setBackground(Color.pink);
            add(north, constraints);
            north.setLayout(new GridBagLayout());

            // Initialize south pane
            constraints.gridx = 1;
            constraints.gridy = 2;
            constraints.gridheight = 1;
            constraints.gridwidth = 1;
            constraints.weighty = 0;
            constraints.weightx = 0;
            constraints.anchor = GridBagConstraints.SOUTH;
            south.setBackground(Color.pink);
            add(south, constraints);
            south.setLayout(new GridBagLayout());
        }

        /**
         * @return an array of all components in the four panes
         */
        public Component[] getAllComponents() {
            Component[] northComps = north.getComponents();
            Component[] southComps = south.getComponents();
            Component[] westComps = west.getComponents();
            Component[] eastComps = east.getComponents();

            Component[] comps = new Component[northComps.length
                    + southComps.length + westComps.length + eastComps.length];
            int i = 0;
            for (Component c : northComps)
                comps[i++] = c;
            for (Component c : southComps)
                comps[i++] = c;
            for (Component c : westComps)
                comps[i++] = c;
            for (Component c : eastComps)
                comps[i++] = c;
            return comps;
        }

        /**
         * Adds a JPanel to the frame as the east panel
         * @param panel the panel to add
         */
        protected void addAsEastPanel(JPanel panel) {
            // Remove east pane if already exists
            if (east != null) remove(east);

            // Set constraints and add east pane
            east = panel;
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.gridx = 1;
            constraints.gridy = 1;
            constraints.gridheight = 1;
            constraints.gridwidth = 1;
            constraints.weighty = 1;
            constraints.weightx = 1;
            east.setBackground(Color.white);
            add(east, constraints);
        }

        /**
         * Adds a Cast Ballot button to the frame, with the given label as
         * instructions
         * @param l the label that tells the user where they're going
         */
        protected void addCastButton(Label l) {
            Spacer PCastInfo = new Spacer(l, south);
            Spacer PCastButton = new Spacer(castButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.weightx = .5;
            constraints.weighty = .5;
            constraints.insets = new Insets(0, 0, 0, 0);
            constraints.gridx = 1;
            constraints.gridy = 0;
            constraints.anchor = GridBagConstraints.LINE_END;
            south.add(PCastInfo, constraints);
            constraints.gridx = 1;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 0, 32, 50);
            south.add(PCastButton, constraints);
        }
        
        /**
         * Adds a Committ Ballot button to the frame, with the given label as
         * instructions
         * @param l the label that tells the user where they're going
         */
        protected void addCommitButton(Label l) {
            Spacer PCastInfo = new Spacer(l, south);
            
            Spacer PCastButton = null;
            
            //The cast button should be sub'd for the commit if we're not using the challenge-commit model
            if(USE_COMMIT_CHALLENGE_MODEL)
            	PCastButton = new Spacer(commitButton, south);
            else
            	PCastButton = new Spacer(castButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.weightx = .5;
            constraints.weighty = .5;
            constraints.insets = new Insets(0, 0, 0, 0);
            constraints.gridx = 1;
            constraints.gridy = 0;
            constraints.anchor = GridBagConstraints.LINE_END;
            south.add(PCastInfo, constraints);
            constraints.gridx = 1;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 0, 32, 50);
            south.add(PCastButton, constraints);
        }

        /**
         * Adds a Next button to the frame, with the given label as instructions
         * @param l the label that tells the user where they're going
         */
        protected void addNextButton(Label l) {
            Spacer PNextInfo = new Spacer(l, south);
            Spacer PNextButton = new Spacer(nextButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.weightx = .5;
            constraints.weighty = .5;
            constraints.insets = new Insets(0, 0, 0, 0);
            constraints.gridx = 1;
            constraints.gridy = 0;
            constraints.anchor = GridBagConstraints.LINE_END;
            south.add(PNextInfo, constraints);
            constraints.gridx = 1;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 0, 32, 50);
            south.add(PNextButton, constraints);
        }

        //#ifdef NONE_OF_ABOVE
        protected void addNextRequireSelectionButton(Label l, String parentCardUID) {
            Button nextRequireSelectionButton = new Button(
            		getNextLayoutUID(), 
            		LiteralStrings.Singleton.get("NEXT_PAGE_BUTTON", language), 
            		"NextPageRequireSelection");
            nextRequireSelectionButton.setIncreasedFontSize(true);
            nextRequireSelectionButton.setSize(nextButton.execute(sizeVisitor));
            nextRequireSelectionButton.setPageNum(-1);
            nextRequireSelectionButton.setParentCardUID(parentCardUID);
        	
        	Spacer PNextInfo = new Spacer(l, south);
            Spacer PNextButton = new Spacer(nextRequireSelectionButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.weightx = .5;
            constraints.weighty = .5;
            constraints.insets = new Insets(0, 0, 0, 0);
            constraints.gridx = 1;
            constraints.gridy = 0;
            constraints.anchor = GridBagConstraints.LINE_END;
            south.add(PNextInfo, constraints);
            constraints.gridx = 1;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 0, 32, 50);
            south.add(PNextButton, constraints);
        }
        //#endif

        /**
         * Adds a Previous button to the frame, with the given label as
         * instructions
         * @param l the label that tells the user where they're going
         */
        protected void addPreviousButton(Label l) {
            Spacer PPreviousInfo = new Spacer(l, south);
            Spacer PPreviousButton = new Spacer(previousButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.weightx = .5;
            constraints.weighty = .5;
            constraints.gridx = 0;
            constraints.gridy = 0;
            constraints.anchor = GridBagConstraints.LINE_START;
            south.add(PPreviousInfo, constraints);
            constraints.gridx = 0;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 50, 32, 0);
            south.add(PPreviousButton, constraints);
        }

        /**
         * Adds a Return button to the frame, with the given label as
         * instructions
         * @param l the label that tells the user where they're going
         * @param target page number of the target
         */
        protected void addReturnButton(Label l, int target) {
        	Button rButton = new Button(getNextLayoutUID(), LiteralStrings.Singleton
                    .get("RETURN_BUTTON", language), "GoToPage");
            rButton.setIncreasedFontSize(true);
            rButton.setSize(rButton.execute(sizeVisitor));
            rButton.setPageNum(target);
            Spacer PReturnInfo = new Spacer(l, south);
            Spacer PReturnButton = new Spacer(rButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.gridx = 0;
            constraints.gridy = 0;
            south.add(PReturnInfo, constraints);
            constraints.gridx = 0;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 0, 32, 0);
            south.add(PReturnButton, constraints);
        }

        //#ifdef NONE_OF_ABOVE
        protected void addReturnRequireSelectionButton(Label l, int target, String parentCardUID) {
        	Button rButton = new Button(
        			getNextLayoutUID(), 
        			LiteralStrings.Singleton.get("RETURN_BUTTON", language), 
        			"GoToPageRequireSelection");
            rButton.setIncreasedFontSize(true);
            rButton.setSize(rButton.execute(sizeVisitor));
            rButton.setPageNum(target);
            rButton.setParentCardUID(parentCardUID);
            Spacer PReturnInfo = new Spacer(l, south);
            Spacer PReturnButton = new Spacer(rButton, south);

            // Setup constraints and add label and button
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.gridx = 0;
            constraints.gridy = 0;
            south.add(PReturnInfo, constraints);
            constraints.gridx = 0;
            constraints.gridy = 1;
            constraints.insets = new Insets(0, 0, 32, 0);
            south.add(PReturnButton, constraints);
        }
        //#endif

        /**
         * Adds the sidebar to the west pane, with the given step highlighted
         * @param step the current step
         */
        protected void addSideBar(int step) {
            GridBagConstraints constraints = new GridBagConstraints();
            Spacer PYouAreNowOn;
            Spacer PMakeYourChoice;
            Spacer PReviewYourChoices;
            Spacer PRecordYourVote;

            // Select correct highlighted label for current step
            if (step == 1)
                PYouAreNowOn = new Spacer(instructionsBold, west);
            else
                PYouAreNowOn = new Spacer(instructions, west);
            if (step == 2)
                PMakeYourChoice = new Spacer(makeYourChoicesBold, west);
            else
                PMakeYourChoice = new Spacer(makeYourChoices, west);
            if (step == 3)
                PReviewYourChoices = new Spacer(reviewYourChoicesBold, west);
            else
                PReviewYourChoices = new Spacer(reviewYourChoices, west);
            if (step == 4)
                PRecordYourVote = new Spacer(recordYourVoteBold, west);
            else
                PRecordYourVote = new Spacer(recordYourVote, west);

            // Add labels to west pane
            constraints.gridy = 0;
            constraints.gridx = 0;
            constraints.weighty = 1;
            constraints.fill = GridBagConstraints.VERTICAL;
            constraints.gridwidth = 1;
            west.add(PYouAreNowOn, constraints);
            constraints.gridx = 0;
            constraints.gridy = 1;
            west.add(PMakeYourChoice, constraints);
            constraints.gridx = 0;
            constraints.gridy = 2;
            west.add(PReviewYourChoices, constraints);
            constraints.gridx = 0;
            constraints.gridy = 3;
            west.add(PRecordYourVote, constraints);
        }

        /**
         * Adds a title Label to this frame
         * @param title the Label title
         * 
         * @return the added title
         */
        protected Spacer addTitle(Label title) {
            // Setup constraints and add title to north pane
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.gridwidth = 1;
            constraints.weightx = 1;
            constraints.weighty = 1;
            constraints.anchor = GridBagConstraints.NORTH;
            title.setCentered(true);
            title.setWidth(WINDOW_WIDTH - 225);
            title.setSize(title.execute(sizeVisitor));
            Spacer label = new Spacer(title, north);
            north.add(label, constraints);
            
            return label;
        }

        /**
         * Adds a title String to this frame
         * @param titleText the String title
         */
        protected Label addTitle(String titleText) {
            Label title = new Label(getNextLayoutUID(), titleText, sizeVisitor);
            addTitle(title);
            
            return title;
        }

    }

    /**
     * Maximum number of candidates on a page
     */
    private static final int MAX_CANDIDATES = 6;

    /**
     * Constant used when determining the font size
     */
    private static int FONT_SIZE_MULTIPLE = 8;

    /**
     * Width of the VoteBox window
     */
    private static final int WINDOW_WIDTH = 1024;

    /**
     * Height of the VoteBox window
     */
    private static final int WINDOW_HEIGHT = 768;

    //private static Layout LAST_LAYOUT = null;
    
    /**
     * Visitor that renders a component and returns an image
     */
    private static ILayoutComponentVisitor<Boolean, BufferedImage> imageVisitor = new ILayoutComponentVisitor<Boolean, BufferedImage>() {
    	
        /**
         * Gets the image from the Background
         */
        public BufferedImage forBackground(Background bg, Boolean... param) {
            return bg.getImage();
        }

        /**
         * Renders a Button
         */
        public BufferedImage forButton(Button button, Boolean... param) {
            int size = 1;
            int fontsize = (size + 1) * FONT_SIZE_MULTIPLE;

            if (button.isIncreasedFontSize()) {
                fontsize += 4;
            }

            return RenderingUtils.renderButton(button.getText(), fontsize,
                    button.isBold(), button.isBoxed(), 
					-1, button.getBackgroundColor());
        }

        /**
         * Renders a Label
         */
        public BufferedImage forLabel(Label l, Boolean... param) {
            int size = 1;
            int fontsize = (size + 1) * FONT_SIZE_MULTIPLE;

            if (l.isIncreasedFontSize()) {
                fontsize += 4;
            }

            return RenderingUtils.renderLabel(l.getText(), l.getInstructions(),
                    l.getDescription(), fontsize, l.getWidth(), l.getColor(), l
                            .isBold(), l.isBoxed(), l.isCentered());
        }

        /**
         * Renders a ReviewButton
         */
        public BufferedImage forReviewButton(ReviewButton rb, Boolean... param) {
            int size = 1;
            int fontsize = (int) ((size + 1) * (FONT_SIZE_MULTIPLE - 1)) - 2;

            BufferedImage buttonImg = RenderingUtils.renderButton(
				rb.getText(), fontsize, rb.isBold(), rb.isBoxed(),
				REVIEW_SCREEN_CAND_WIDTH,
				rb.getBackgroundColor());
            
			// render party information [dsandler]
			String aux = rb.getAuxText();
			if (aux != null && REVIEW_SCREEN_SHOW_PARTY && !aux.equals("")) {
				if (REVIEW_SCREEN_PARENTHESIZE_PARTY) 
					aux = "(" + aux + ")";

				Graphics2D graf = buttonImg.createGraphics();
				graf.setRenderingHint(
					RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
				
				Font font = new Font(RenderingUtils.FONT_NAME, Font.PLAIN, fontsize);
				graf.setFont(font);
				graf.setColor(Color.BLACK);

				Rectangle2D partyTextBounds = font.getStringBounds(aux,
						new FontRenderContext(null, true, true));

				// draw it right-aligned
				graf.drawString(aux,
					(int)(buttonImg.getWidth() - partyTextBounds.getWidth() - 10), 
					(int)(partyTextBounds.getHeight() + 8));
			}

			return buttonImg;
        }

        /**
         * Renders a ReviewLabel
         */
        public BufferedImage forReviewLabel(ReviewLabel rl, Boolean... param) {
            int size = 1;
            int fontsize = (int) ((size + 1) * (FONT_SIZE_MULTIPLE - 1));

            return RenderingUtils.renderLabel(rl.getText(), "", "", fontsize,
                    //rl.getWidth(), 
					100,
					rl.getColor(), rl.isBold(), rl.isBoxed(), rl
                            .isCentered());
        }

        /**
         * Renders a ToggleButton
         */
        public BufferedImage forToggleButton(ToggleButton tb, Boolean... param) {
            int size = 1;

            int fontsize = (size + 1) * FONT_SIZE_MULTIPLE;
            if (tb.isIncreasedFontSize()) {
                fontsize += 4;
            }

            return RenderingUtils.renderToggleButton(
            		tb.getText(), tb.getSecondLine(), tb.getParty(), fontsize,
            		tb.getWidth(), tb.isBold(), param[0]);
        }

        /**
         * Returns null
         */
        public BufferedImage forToggleButtonGroup(ToggleButtonGroup tbg,
                Boolean... param) {
            return null;
        }

		public BufferedImage forVVPATReviewButton(ReviewButton rb, Boolean... param) {
			int size = 1;
            int fontsize = (int) ((size + 1) * (VVPAT_FONT_SIZE_MULTIPLE - 1)) - 2;
            
            BufferedImage buttonImg = RenderingUtils.renderButton(
				rb.getText(), fontsize, rb.isBold(), rb.isBoxed(),
				VVPAT_CAND_WIDTH,
				rb.getBackgroundColor());
            
            BufferedImage xImg = null;
            
            //TODO: Make this less of a hack... for instance, working in non-English would be nice
            if(!rb.getText().contains("None"))
            	xImg = RenderingUtils.renderButton("[X]", fontsize, false, false, 25, rb.getBackgroundColor());
            else
            	xImg = RenderingUtils.renderButton("[ ]", fontsize, false, false, 25, rb.getBackgroundColor());
            
            BufferedImage textPlusX = new BufferedImage(buttonImg.getWidth() + xImg.getWidth() + 10, 
            		(int)Math.max(buttonImg.getHeight(), xImg.getHeight()), BufferedImage.TYPE_BYTE_BINARY);
            
            Graphics g = textPlusX.getGraphics();
            g.setColor(Color.white);
            g.fillRect(0, 0, textPlusX.getWidth(), textPlusX.getHeight());
            g.drawImage(xImg, 0, textPlusX.getHeight()/2 - xImg.getHeight()/2, null);
            g.drawImage(buttonImg, xImg.getWidth() + 10, textPlusX.getHeight()/2 - buttonImg.getHeight()/2, null);
            
            String titleStr = "" + rb.getPageNum();
            
            BufferedImage titleImg = RenderingUtils.renderButton(titleStr, fontsize, true, false, VVPAT_CAND_WIDTH, rb.getBackgroundColor());
            
            BufferedImage fullImg = new BufferedImage((int)Math.max(textPlusX.getWidth(), titleImg.getWidth()),
            		titleImg.getHeight() + 5 + textPlusX.getHeight(), BufferedImage.TYPE_BYTE_BINARY);
            
            g = fullImg.getGraphics();
            g.setColor(Color.white);
            g.fillRect(0, 0, fullImg.getWidth(), fullImg.getHeight());
            g.drawImage(titleImg, 0, 0, null);
            g.drawImage(textPlusX, 0, 5 + titleImg.getHeight(), null);
            
			return fullImg;
		}
    };

    /**
     * Visitor that calculates the size of a component
     */
    private static ILayoutComponentVisitor<Object, Dimension> sizeVisitor = new ILayoutComponentVisitor<Object, Dimension>() {

        /**
         * Gets the size of the Background
         */
        public Dimension forBackground(Background bg, Object... param) {
            return new Dimension(bg.getWidth(), bg.getHeight());
        }

        /**
         * Calculates the size of the Button
         */
        public Dimension forButton(Button button, Object... param) {
            int size = 1;
            int fontsize = (size + 1) * FONT_SIZE_MULTIPLE;

            if (button.isIncreasedFontSize()) {
                fontsize += 4;
            }

            return RenderingUtils.getButtonSize(button.getText(), fontsize,
                    button.isBold());
        }

        /**
         * Calculates the size of the Label
         */
        public Dimension forLabel(Label l, Object... param) {
            int size = 1;
            int fontsize = (size + 1) * FONT_SIZE_MULTIPLE;
            if (l.isIncreasedFontSize()) {
                fontsize += 4;
            }
            ;

            return RenderingUtils.getLabelSize(l.getText(),
                    l.getInstructions(), l.getDescription(), fontsize, l
                            .getWidth(), l.isBold(), l.isCentered());
        }

        /**
         * Calculates the size of the ReviewButton
         */
        public Dimension forReviewButton(ReviewButton rb, Object... param) {
            int size = 1;
            int fontsize = (int) ((size + .5) * (FONT_SIZE_MULTIPLE - 2));

            return RenderingUtils.getButtonSize(rb.getText(), fontsize, rb
                    .isBold());
        }

        /**
         * Calculates the size of the ReviewLabel
         */
        public Dimension forReviewLabel(ReviewLabel rl, Object... param) {
            int size = 1;
            int fontsize = (int) ((size + .5) * (FONT_SIZE_MULTIPLE - 2));

            return RenderingUtils.getLabelSize(rl.getText(), "", "", fontsize,
                    rl.getWidth(), rl.isBold(), rl.isCentered());
        }

        /**
         * Calculates the size of the ToggleButton
         */
        public Dimension forToggleButton(ToggleButton tb, Object... param) {
            int size = 1;

            int fontsize = (size + 1) * FONT_SIZE_MULTIPLE;
            if (tb.isIncreasedFontSize()) {
                fontsize += 4;
            }

            return RenderingUtils
                    .getToggleButtonSize(tb.getText(), tb.getSecondLine(), tb
                            .getParty(), fontsize, RACE_DESCRIPTION_WIDTH, tb.isBold());
        }

        /**
         * Returns null
         */
        public Dimension forToggleButtonGroup(ToggleButtonGroup tbg,
                Object... param) {
            return null;
        }

		public Dimension forVVPATReviewButton(ReviewButton rb, Object... param) {
			return null;
		}
    };

    /**
     * The language this LayoutManager is responsible for
     */
    private Language language;

    /**
     * A Common Cast Button
     */
    protected Button castButton;
    
    /**
     * A Common Commit Button
     */
    protected Button commitButton;
    
    /**
     * A Common Challenge Button
     */
    protected Button challengeButton;

    /**
     * A Common NextButton
     */
    protected Button nextButton;

    /**
     * A Common PreviousButton
     */
    protected Button previousButton;

    /**
     * A Common Return Button
     */
    protected Button returnButton;

    /**
     * Instructions label for the sidebar
     */
    protected Label instructions;

    /**
     * Make your choices label for the sidebar
     */
    protected Label makeYourChoices;

    /**
     * Review your choices label for the sidebar
     */
    protected Label reviewYourChoices;

    /**
     * Record your vote label for the sidebar
     */
    protected Label recordYourVote;

    /**
     * Bold Instructions label for the sidebar
     */
    protected Label instructionsBold;

    /**
     * Bold Make your choices label for the sidebar
     */
    protected Label makeYourChoicesBold;

    /**
     * Bold Review your choices label for the sidebar
     */
    protected Label reviewYourChoicesBold;

    /**
     * Bold Record your vote label for the sidebar
     */
    protected Label recordYourVoteBold;

    /**
     * Next race label
     */
    protected Label nextInfo;

    /**
     * Previous race label
     */
    protected Label previousInfo;

    /**
     * Return label
     */
    protected Label returnInfo;

    /**
     * More candidates label
     */
    protected Label moreCandidatesInfo;

    /**
     * Instructions for a race
     */
    protected Label raceInstructions;

    /**
     * The background for this layout
     */
    protected Background background;

    /**
     * Background for this layout, without the sidebar
     */
    protected Background simpleBackground;

    /**
     * Creates a new PsychLayoutManager and initializes many of the "common"
     * components, such as the next button.
     */
    public PsychLayoutManager(Language language, int numCardsPerReviewPage, int fontSize, boolean commitChallenge) {
        this.language = language;
        
        CARDS_PER_REVIEW_PAGE = numCardsPerReviewPage;
    	FONT_SIZE_MULTIPLE = fontSize;
    	USE_COMMIT_CHALLENGE_MODEL = commitChallenge;

        instructions = new Label(getNextLayoutUID(), LiteralStrings.Singleton
                .get("SIDEBAR_INSTRUCTIONS", language));
        instructions.setWidth(225);
        instructions.setIncreasedFontSize(true);
        instructions.setColor(new Color(72, 72, 72));
        instructions.setSize(instructions.execute(sizeVisitor));

        makeYourChoices = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("SIDEBAR_MAKE_CHOICES", language));
        makeYourChoices.setWidth(225);
        makeYourChoices.setIncreasedFontSize(true);
        makeYourChoices.setColor(new Color(72, 72, 72));
        makeYourChoices.setSize(makeYourChoices.execute(sizeVisitor));

        reviewYourChoices = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton
                        .get("SIDEBAR_REVIEW_CHOICES", language));
        reviewYourChoices.setWidth(225);
        reviewYourChoices.setIncreasedFontSize(true);
        reviewYourChoices.setColor(new Color(72, 72, 72));
        reviewYourChoices.setSize(reviewYourChoices.execute(sizeVisitor));

        recordYourVote = new Label(getNextLayoutUID(), LiteralStrings.Singleton
                .get("SIDEBAR_RECORD_VOTE", language));
        recordYourVote.setWidth(225);
        recordYourVote.setIncreasedFontSize(true);
        recordYourVote.setColor(new Color(72, 72, 72));
        recordYourVote.setSize(recordYourVote.execute(sizeVisitor));

        instructionsBold = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get(
                        "SIDEBAR_INSTRUCTIONS_HIGHLIGHTED", language));
        instructionsBold.setWidth(225);
        instructionsBold.setIncreasedFontSize(true);
        instructionsBold.setColor(Color.WHITE);
        instructionsBold.setBold(true);
        instructionsBold.setSize(instructionsBold.execute(sizeVisitor));

        makeYourChoicesBold = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get(
                        "SIDEBAR_MAKE_CHOICES_HIGHLIGHTED", language));
        makeYourChoicesBold.setWidth(225);
        makeYourChoicesBold.setIncreasedFontSize(true);
        makeYourChoicesBold.setColor(Color.WHITE);
        makeYourChoicesBold.setBold(true);
        makeYourChoicesBold.setSize(makeYourChoicesBold.execute(sizeVisitor));

        reviewYourChoicesBold = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get(
                        "SIDEBAR_REVIEW_CHOICES_HIGHLIGHTED", language));
        reviewYourChoicesBold.setWidth(225);
        reviewYourChoicesBold.setIncreasedFontSize(true);
        reviewYourChoicesBold.setColor(Color.WHITE);
        reviewYourChoicesBold.setBold(true);
        reviewYourChoicesBold.setSize(reviewYourChoicesBold
                .execute(sizeVisitor));

        recordYourVoteBold = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("SIDEBAR_RECORD_VOTE_HIGHLIGHTED",
                        language));
        recordYourVoteBold.setWidth(225);
        recordYourVoteBold.setIncreasedFontSize(true);
        recordYourVoteBold.setColor(Color.WHITE);
        recordYourVoteBold.setBold(true);
        recordYourVoteBold.setSize(recordYourVoteBold.execute(sizeVisitor));

        nextButton = new Button(getNextLayoutUID(), LiteralStrings.Singleton
                .get("NEXT_PAGE_BUTTON", language), "NextPage");
        nextButton.setIncreasedFontSize(true);
        nextButton.setSize(nextButton.execute(sizeVisitor));

        previousButton = new Button(getNextLayoutUID(),
                LiteralStrings.Singleton.get("PREVIOUS_PAGE_BUTTON", language),
                "PreviousPage");
        previousButton.setIncreasedFontSize(true);
        previousButton.setSize(previousButton.execute(sizeVisitor));

        returnButton = new Button(getNextLayoutUID(), LiteralStrings.Singleton
                .get("RETURN_BUTTON", language), "GoToPage");
        returnButton.setIncreasedFontSize(true);
        returnButton.setSize(returnButton.execute(sizeVisitor));

        castButton = new Button(getNextLayoutUID(), LiteralStrings.Singleton
                .get("CAST_BUTTON", language), "CastBallot");
        castButton.setIncreasedFontSize(true);
        castButton.setSize(castButton.execute(sizeVisitor));
        
        commitButton = new Button(getNextLayoutUID(), LiteralStrings.Singleton
                .get("COMMIT_BUTTON", language), "CommitBallot");
        commitButton.setIncreasedFontSize(true);
        commitButton.setSize(commitButton.execute(sizeVisitor));
        
        challengeButton = new Button(getNextLayoutUID(), LiteralStrings.Singleton
                .get("CHALLENGE_BUTTON", language), "Challenge");
        challengeButton.setIncreasedFontSize(true);
        challengeButton.setSize(challengeButton.execute(sizeVisitor));

        nextInfo = new Label(getNextLayoutUID(), LiteralStrings.Singleton.get(
                "FORWARD_NEXT_RACE", language), sizeVisitor);
        previousInfo = new Label(getNextLayoutUID(), LiteralStrings.Singleton
                .get("BACK_PREVIOUS_RACE", language), sizeVisitor);
        returnInfo = new Label(getNextLayoutUID(), LiteralStrings.Singleton
                .get("RETURN_REVIEW_SCREEN", language), sizeVisitor);
        moreCandidatesInfo = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("MORE_CANDIDATES", language),
                sizeVisitor);

        raceInstructions = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("RACE_INSTRUCTIONS", language),
                sizeVisitor);

        background = makeBackground();
        simpleBackground = makeSimpleBackground();
    }
    
    /**
     * @return the image rendering visitor
     */
    @Override
    public ILayoutComponentVisitor<Boolean, BufferedImage> getImageVisitor() {
        return imageVisitor;
    }

    /**
     * @return the language
     */
    @Override
    public Language getLanguage() {
        return language;
    }

    /**
     * @return the size calculating visitor
     */
    @Override
    public ILayoutComponentVisitor<Object, Dimension> getSizeVisitor() {
        return sizeVisitor;
    }

    @Override
    public ArrayList<JPanel> makeCardPage(ACard card) {
        return card.layoutCard(this, new PsychCardLayout()).makeIntoPanels();
    }

    /**
     * Makes the layout from the given ballot, as specified by the Psychology
     * department.
     */
    @Override
    public Layout makeLayout(Ballot ballot) {
        assignUIDsToBallot(ballot);
        Layout layout = new Layout();
        if (ballot.getLanguages().size() > 1) {
            layout.getPages()
                    .add(makeLanguageSelectPage(ballot.getLanguages()));
            layout.getPages().add(makeInstructionsPage(true));
        } else {
            layout.getPages().add(makeInstructionsPage(false));
        }
        int cnt = 1;
        for (ACard card : ballot.getCards()) {
            layout.getPages().addAll(
                    makeCardLayoutPage(card, false, 0, cnt, ballot.getCards()
                            .size()));
            ++cnt;
        }
        //layout.getPages().add(new Page());
        int reviewPageNum = layout.getPages().size();

        HashMap<Integer, Integer> pageTargets = new HashMap<Integer, Integer>();
        
        for (int raceN = 0; raceN < ballot.getCards().size(); raceN++) {
        	ACard card = ballot.getCards().get(raceN);
        	//correctly deal with boundary conditions: size = 1, size = CARDS_PER_REVIEW_PAGE or a multiple thereof
        	int additionalReviewPages = (ballot.getCards().size() - 1) / CARDS_PER_REVIEW_PAGE;
        	//there are 2 pages after the last review screen: Cast and Success 
        	int reviewCardNumber = raceN + 3;
        	if (USE_COMMIT_CHALLENGE_MODEL){
        		//there is an additional page between Cast and Success: Challenge
        		reviewCardNumber++;
        	}
            pageTargets.put(raceN, reviewPageNum + additionalReviewPages + reviewCardNumber);
            int currentReviewPage = raceN / CARDS_PER_REVIEW_PAGE;
            layout.getPages().addAll(
                    makeCardLayoutPage(card, true, reviewPageNum + currentReviewPage, 0, 0));
        }
        
        List<Page> reviewPages = makeReviewPage(ballot, pageTargets);
        
        layout.getPages().addAll(reviewPageNum, reviewPages);
        
        for(Page reviewPage : reviewPages)
        	reviewPage.markAsReviewPage();
        
        layout.getPages().add(reviewPageNum + (ballot.getCards().size() / CARDS_PER_REVIEW_PAGE) + 1, makeCastPage());
        
        if (USE_COMMIT_CHALLENGE_MODEL){
        	layout.getPages().add(reviewPageNum + (ballot.getCards().size() / CARDS_PER_REVIEW_PAGE) + 2, makeChallengePage());
        	reviewPageNum++;
        }
        
        layout.getPages().add(reviewPageNum + (ballot.getCards().size() / CARDS_PER_REVIEW_PAGE) + 2, makeSuccessPage());
        
        layout.getPages().add(makeOverrideCancelPage());
        layout.setOverrideCancelPage(layout.getPages().size()-1);
        layout.getPages().add(makeOverrideCastPage());
        layout.setOverrideCastPage(layout.getPages().size()-1);
        
        if (USE_COMMIT_CHALLENGE_MODEL){
        	layout.getPages().add(makeResponsePage());
        	layout.setReponsePage(layout.getPages().size()-1);
        }
        
        //LAST_LAYOUT = layout;
        
        //#ifdef NONE_OF_ABOVE
        // Get the number of cards
        int numCards = ballot.getCards().size();
        // Add a "no-selection alert page" for each race
        for (int raceN = 0; raceN < numCards; raceN++) {
        	layout.getPages().add(makeNoSelectionPage(raceN+1));
        }
        // Add another no-selection alert page for each race-review screen
        for (int raceN = 0; raceN < numCards; raceN++) {
        	layout.getPages().add(makeNoSelectionPage(raceN+numCards+4));
        }
        //#endif
        
        return layout;
    }

    /**
     * Makes a Background for this LayoutManager.
     * @return the Background
     */
    protected Background makeBackground() {
        PsychLayoutPanel frame = new PsychLayoutPanel();

        Label instructionsTitle = new Label("L0", LiteralStrings.Singleton.get(
                "INSTRUCTIONS_TITLE", language));
        instructionsTitle.setCentered(true);
        instructionsTitle.setSize(instructionsTitle.execute(sizeVisitor));
        frame.addTitle(instructionsTitle);
        frame.addSideBar(1);
        frame.addNextButton(nextInfo);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label("L0", LiteralStrings.Singleton.get(
                "INSTRUCTIONS", language), sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        frame.validate();
        frame.pack();

        BufferedImage image = new BufferedImage(WINDOW_WIDTH, WINDOW_HEIGHT,
                BufferedImage.TYPE_INT_RGB);
        Graphics2D graphs = (Graphics2D) image.getGraphics();
        graphs.setColor(Color.WHITE);
        graphs.fillRect(0, 0, WINDOW_WIDTH, WINDOW_HEIGHT);
        graphs.setColor(new Color(48, 149, 242));
        graphs.fillRect(0, 0, frame.west.getWidth(), WINDOW_HEIGHT);
        graphs.setColor(Color.PINK);
        graphs.fillRect(frame.west.getWidth(), 0, frame.north.getWidth(),
                frame.north.getHeight());
        graphs.fillRect(frame.west.getWidth(), WINDOW_HEIGHT
                - frame.south.getHeight(), frame.south.getWidth(), frame.south
                .getHeight());
        return new Background(getNextLayoutUID(), image);
    }

    /**
     * Makes a Page that contains a Card, by creating the page as normal and
     * then calling into the visitor to handle the Card-specific components
     * @param card the card
     * @param jump whether this page is a jump page from the review screen
     * @param target page number of the review screen
     * @param idx the index of the card
     * @param total total number of cards
     * @return the completed Page
     */
    protected ArrayList<Page> makeCardLayoutPage(ACard card, boolean jump,
            int target, int idx, int total) {
        ArrayList<JPanel> cardPanels = makeCardPage(card);
        ArrayList<Page> pages = new ArrayList<Page>();
        
        @SuppressWarnings("unused")
		Label title = null;
        
        for (int i = 0; i < cardPanels.size(); i++) {
            // Setup card frame
            PsychLayoutPanel cardFrame = new PsychLayoutPanel();
            title = cardFrame.addTitle(card.getTitle(language));
            cardFrame.addSideBar(2);
            if (!jump) {
                if (i > 0) {
                    cardFrame.addPreviousButton((Label) moreCandidatesInfo.clone());
                }
                else if (idx == 1) {
                    cardFrame.addPreviousButton(new Label(getNextLayoutUID(),
                            LiteralStrings.Singleton.get("BACK_INSTRUCTIONS",
                                    language), sizeVisitor));
                }
                else {
                    cardFrame.addPreviousButton(previousInfo);
                }
                if (i < cardPanels.size() - 1) {
                	//#ifdef NONE_OF_ABOVE
            		cardFrame.addNextRequireSelectionButton((Label) moreCandidatesInfo.clone(), card.getUID());
            		//#endif
            		//#ifndef NONE_OF_ABOVE
                    cardFrame.addNextButton((Label) moreCandidatesInfo.clone());
            		//#endif
                }
                else if (idx == total) {
                	Label forward = new Label(
                			getNextLayoutUID(),
                            LiteralStrings.Singleton.get("FORWARD_REVIEW", language), 
                            sizeVisitor);
                	//#ifdef NONE_OF_ABOVE
                    cardFrame.addNextRequireSelectionButton(forward, card.getUID());
                     //#endif
            		//#ifndef NONE_OF_ABOVE
                    cardFrame.addNextButton(forward);
                    //#endif
                }
                else {
                	//#ifdef NONE_OF_ABOVE
                	cardFrame.addNextRequireSelectionButton(nextInfo, card.getUID());
                	//#endif
            		//#ifndef NONE_OF_ABOVE
                    cardFrame.addNextButton(nextInfo);
                    //#endif
                }
            } else {
            	//#ifdef NONE_OF_ABOVE
                cardFrame.addReturnRequireSelectionButton(returnInfo, target, card.getUID());
            	//#endif
        		//#ifndef NONE_OF_ABOVE
                cardFrame.addReturnButton(returnInfo, target);
                //#endif
                if (i > 0)
                    cardFrame.addPreviousButton((Label) moreCandidatesInfo.clone());
                if (i < cardPanels.size() - 1)
                    cardFrame.addNextButton((Label) moreCandidatesInfo.clone());
            }

            // Add card's content as east pane
            cardFrame.addAsEastPanel(cardPanels.get(i));

            // Add instructions
            GridBagConstraints constraints = new GridBagConstraints();
            constraints.anchor = GridBagConstraints.NORTH;
            constraints.fill = GridBagConstraints.VERTICAL;
            constraints.gridy = 1;
            constraints.gridx = 0;
            constraints.weightx = 1;
            constraints.weighty = 1;
            Spacer instspacer = new Spacer(raceInstructions, cardFrame.north);
            cardFrame.north.add(instspacer, constraints);
            cardFrame.validate();
            cardFrame.pack();

            // Add all components to a Page, with their updated positions
            Page cardPage = new Page();
            cardPage.getComponents().add(background);
            cardPage.setBackgroundLabel(background.getUID());
            for (Component c : cardFrame.getAllComponents()) {
                Spacer s = (Spacer) c;
                s.updatePosition();
                if (!(s.getComponent() instanceof ToggleButton)){
                    cardPage.getComponents().add(s.getComponent());
                }//if
            }
            pages.add(cardPage);
        }
        return pages;
    }

    @Override
    protected Page makeCastPage() {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label recordTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("RECORD_TITLE", language));
        recordTitle.setBold(true);
        recordTitle.setCentered(true);
        recordTitle.setSize(recordTitle.execute(sizeVisitor));
        frame.addTitle(recordTitle);
        frame.addSideBar(4);
        frame.addPreviousButton(new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("BACK_REVIEW", language),
                sizeVisitor));
        frame.addCommitButton(new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("NEXT_PAGE_BUTTON", language),
                sizeVisitor));

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("RECORD_INSTRUCTIONS", language),
                sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(background);
        page.setBackgroundLabel(background.getUID());

        for (Component c : frame.getAllComponents()) {
            Spacer s = (Spacer) c;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }

    @Override
    protected Page makeInstructionsPage(boolean hadLanguageSelect) {
        PsychLayoutPanel frame = new PsychLayoutPanel();

        Label instructionsTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("INSTRUCTIONS_TITLE", language));
        instructionsTitle.setCentered(true);
        instructionsTitle.setSize(instructionsTitle.execute(sizeVisitor));
        frame.addTitle(instructionsTitle);
        frame.addSideBar(1);
        frame.addNextButton(new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("FORWARD_FIRST_RACE", language),
                sizeVisitor));
        if (hadLanguageSelect)
            frame.addPreviousButton(new Label(getNextLayoutUID(),
                    LiteralStrings.Singleton.get("BACK_LANGUAGE_SELECT",
                            language), sizeVisitor));

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("INSTRUCTIONS", language),
                sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        frame.validate();
        frame.pack();

        Page page = new Page();
        if (background != null) {
            page.getComponents().add(background);
            page.setBackgroundLabel(background.getUID());
        }

        for (Component c : frame.getAllComponents()) {
            Spacer s = (Spacer) c;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }

    @Override
    protected Page makeLanguageSelectPage(ArrayList<Language> languages) {
        PsychLayoutPanel frame = new PsychLayoutPanel();

        frame.addTitle(LiteralStrings.Singleton.get("LANGUAGE_SELECT_TITLE",
                language));
        frame.addSideBar(1);
        frame.addNextButton(new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("FORWARD_INSTRUCTIONS", language),
                sizeVisitor));

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        GridBagConstraints eastConstraints = new GridBagConstraints();

        eastConstraints.anchor = GridBagConstraints.SOUTH;
        eastConstraints.fill = GridBagConstraints.VERTICAL;
        int ycoord = 0; // the ycoordinate of where to add in gridbag
        eastConstraints.gridy = ycoord;
        eastConstraints.gridx = 0;

        ycoord++;
        Label title = new Label(getNextLayoutUID(), LiteralStrings.Singleton
                .get("LANGUAGE_SELECT_TITLE", language));
        title.setWidth(LANG_SELECT_WIDTH);
        title.setBoxed(true);
        title.setCentered(true);
        title.setSize(title.execute(sizeVisitor));

        Spacer PTitle = new Spacer(title, east);
        east.add(PTitle, eastConstraints);

        ToggleButtonGroup tbg = new ToggleButtonGroup("LanguageSelect");
        for (Language lang : languages) {
            LanguageButton button = new LanguageButton(getNextLayoutUID(), lang
                    .getName());
            button.setLanguage(lang);
            button.setWidth(LANG_SELECT_WIDTH);
            button.setIncreasedFontSize(true);
            button.setSize(button.execute(sizeVisitor));
            eastConstraints.gridy = ycoord++;
            eastConstraints.gridx = 0;
            Spacer PDrawable = new Spacer(button, east);
            east.add(PDrawable, eastConstraints);
            tbg.getButtons().add(button);
        }
        east.add(new Spacer(tbg, east));
        frame.addAsEastPanel(east);

        GridBagConstraints constraints = new GridBagConstraints();
        constraints.anchor = GridBagConstraints.NORTH;
        constraints.fill = GridBagConstraints.VERTICAL;
        constraints.gridy = 1;
        constraints.gridx = 0;
        constraints.weightx = 1;
        constraints.weighty = 1;
        Label instLabel = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("LANGUAGE_SELECT_INSTRUCTIONS",
                        language), sizeVisitor);
        Spacer instspacer = new Spacer(instLabel, frame.north);
        frame.north.add(instspacer, constraints);

        frame.validate();
        frame.pack();

        Page page = new Page();
        if (background != null) {
            page.getComponents().add(background);
            page.setBackgroundLabel(background.getUID());
        }

        for (Component c : frame.getAllComponents()) {
            Spacer s = (Spacer) c;
            s.updatePosition();
            if (!(s.getComponent() instanceof ToggleButton))
                page.getComponents().add(s.getComponent());
        }
        return page;
    }

    @Override
    protected Page makeOverrideCancelPage() {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label successTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_CANCEL_TITLE", language));
        successTitle.setBold(true);
        successTitle.setCentered(true);
        successTitle.setSize(successTitle.execute(sizeVisitor));
        frame.addTitle(successTitle);
        frame.remove(frame.west);

        Label reviewInstructions = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_CANCEL_INSTRUCTIONS",
                        language), sizeVisitor);
        GridBagConstraints c = new GridBagConstraints();
        c.anchor = GridBagConstraints.NORTH;
        c.fill = GridBagConstraints.VERTICAL;
        c.gridy = 1;
        c.gridx = 0;
        c.weightx = 1;
        c.weighty = 1;
        Spacer instspacer = new Spacer(reviewInstructions, frame.north);
        frame.north.add(instspacer, c);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        c = new GridBagConstraints();

        Button confirmBtn = new Button(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_CANCEL_CONFIRM",
                        language), "OverrideCancelConfirm");
        confirmBtn.setIncreasedFontSize(true);
        confirmBtn.setSize(confirmBtn.execute(sizeVisitor));
        Spacer sp = new Spacer(confirmBtn, east);
        east.add(sp, c);
        
        Button denyBtn = new Button(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_DENY",
                        language), "OverrideCancelDeny");
        denyBtn.setIncreasedFontSize(true);
        denyBtn.setSize(denyBtn.execute(sizeVisitor));
        sp = new Spacer(denyBtn, east);
        c.gridy = 1;
        c.insets = new Insets(50, 0, 0, 0);
        east.add(sp, c);
        
        frame.addAsEastPanel(east);
        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(simpleBackground);
        page.setBackgroundLabel(simpleBackground.getUID());

        for (Component co : frame.getAllComponents()) {
            Spacer s = (Spacer) co;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }

    @Override
    protected Page makeOverrideCastPage() {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label successTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_CAST_TITLE", language));
        successTitle.setBold(true);
        successTitle.setCentered(true);
        successTitle.setSize(successTitle.execute(sizeVisitor));
        frame.addTitle(successTitle);
        frame.remove(frame.west);

        Label reviewInstructions = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_CAST_INSTRUCTIONS",
                        language), sizeVisitor);
        GridBagConstraints c = new GridBagConstraints();
        c.anchor = GridBagConstraints.NORTH;
        c.fill = GridBagConstraints.VERTICAL;
        c.gridy = 1;
        c.gridx = 0;
        c.weightx = 1;
        c.weighty = 1;
        Spacer instspacer = new Spacer(reviewInstructions, frame.north);
        frame.north.add(instspacer, c);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        c = new GridBagConstraints();

        Button confirmBtn = new Button(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_CAST_CONFIRM",
                        language), "OverrideCastConfirm");
        confirmBtn.setIncreasedFontSize(true);
        confirmBtn.setSize(confirmBtn.execute(sizeVisitor));
        Spacer sp = new Spacer(confirmBtn, east);
        east.add(sp, c);
        
        Button denyBtn = new Button(getNextLayoutUID(),
                LiteralStrings.Singleton.get("OVERRIDE_DENY",
                        language), "OverrideCastDeny");
        denyBtn.setIncreasedFontSize(true);
        denyBtn.setSize(denyBtn.execute(sizeVisitor));
        sp = new Spacer(denyBtn, east);
        c.gridy = 1;
        c.insets = new Insets(50, 0, 0, 0);
        east.add(sp, c);
        
        frame.addAsEastPanel(east);
        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(simpleBackground);
        page.setBackgroundLabel(simpleBackground.getUID());

        for (Component co : frame.getAllComponents()) {
            Spacer s = (Spacer) co;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }

    @Override
    protected ArrayList<Page> makeReviewPage(Ballot ballot, HashMap<Integer, Integer> pageTargets) {

    	ArrayList<Page> reviewPages = new ArrayList<Page>();
    	int position = 0; //the current position in the list of race review things

    	//inline modification of the amount of review screens
    	int numReviewPages = 1; //starting value; increases if there is a need.
    	for ( int reviewPageNum = 0; reviewPageNum < numReviewPages; reviewPageNum++) {
    		//set up review frame
    		PsychLayoutPanel frame = new PsychLayoutPanel();
    		Label reviewTitle = new Label(getNextLayoutUID(), LiteralStrings.Singleton
    				.get("REVIEW_TITLE", language));
    		reviewTitle.setBold(true);
    		reviewTitle.setCentered(true);
    		reviewTitle.setSize(reviewTitle.execute(sizeVisitor));
    		frame.addTitle(reviewTitle);
    		frame.addSideBar(3);
    		
    		if (reviewPageNum == 0) // first page
    			frame.addPreviousButton(new Label(getNextLayoutUID(),
    	                LiteralStrings.Singleton.get("BACK_LAST_RACE", language),
    	                sizeVisitor));
    		else
    			frame.addPreviousButton(new Label(getNextLayoutUID(), LiteralStrings.Singleton
    					.get("PREVIOUS_PAGE_BUTTON", language), sizeVisitor));
    		if (position == ballot.getCards().size() - 1) //last page, see bottom conditional
    			frame.addNextButton(new Label(getNextLayoutUID(),
    	                LiteralStrings.Singleton.get("FORWARD_RECORD", language),
    	                sizeVisitor));
    		else
    			frame.addNextButton(new Label(getNextLayoutUID(), LiteralStrings.Singleton
    					.get("NEXT_PAGE_BUTTON", language), sizeVisitor));

    		//add content as east pane
    		JPanel east = new JPanel();
    		east.setLayout(new GridBagLayout());
    		GridBagConstraints c = new GridBagConstraints();
    		east.setLayout(new GridBagLayout());
    		c.gridx = 0;
    		c.gridy = 0;
    		c.anchor = GridBagConstraints.FIRST_LINE_START;
    		c.fill = GridBagConstraints.HORIZONTAL;
    		int align = 0;

    		//current review button number
    		int cnt = 0; 

    		int columnLength = (int)Math.ceil(ballot.getCards().size() / REVIEW_SCREEN_NUM_COLUMNS);

    		for (int i = position; i < ballot.getCards().size(); i++) {

    			ACard card = ballot.getCards().get(i);
    			ReviewButton rl = new ReviewButton(getNextLayoutUID(), card.getReviewTitle(language), "GoToPage", sizeVisitor);
    			rl.setBold(true);
    			rl.setBoxed(false);
    			rl.setWidth(REVIEW_SCREEN_RACE_WIDTH);
    			rl.setPageNum(pageTargets.get(position));
    			ReviewButton rb = new ReviewButton(card.getUID(), card.getReviewBlankText(language), "GoToPage", sizeVisitor);
    			rb.setBoxed(false);
    			rb.setWidth(REVIEW_SCREEN_CAND_WIDTH);
    			rb.setPageNum(pageTargets.get(position));

    			Spacer rlSpacer = new Spacer(rl, east);
    			c.gridx = align;
    			east.add(rlSpacer, c);

    			Spacer rbSpacer = new Spacer(rb, east);
    			c.gridx = c.gridx + 1;
    			east.add(rbSpacer, c);

    			cnt++;
    			c.gridy++;

    			if (cnt > columnLength) {
    				cnt = 0;
    				align++;
    				c.gridy = 0;
    				c.anchor = GridBagConstraints.FIRST_LINE_END;
    			}
    			position++;
    			if (i % CARDS_PER_REVIEW_PAGE >= CARDS_PER_REVIEW_PAGE - 1) //number of races to put on each card
    				break;
    		}
    		frame.addAsEastPanel(east);

    		//add instructions
    		Label reviewInstructions = new Label(getNextLayoutUID(), LiteralStrings.Singleton.get("REVIEW_INSTRUCTIONS", language), sizeVisitor);
    		GridBagConstraints constraints = new GridBagConstraints();
    		constraints.anchor = GridBagConstraints.NORTH;
    		constraints.fill = GridBagConstraints.VERTICAL;
    		constraints.gridy = 1;
    		constraints.gridx = 0;
    		constraints.weightx = 1;
    		constraints.weighty = 1;
    		Spacer instspacer = new Spacer(reviewInstructions, frame.north);
    		frame.north.add(instspacer, constraints);

    		frame.validate();
    		frame.pack();

    		//add to a Page
    		Page cardPage = new Page();
    		cardPage.getComponents().add(background);
    		cardPage.setBackgroundLabel(background.getUID());

    		for (Component cmp : frame.getAllComponents()) {
    			Spacer s = (Spacer) cmp;
    			s.updatePosition();
    			cardPage.getComponents().add(s.getComponent());
    		}
    		reviewPages.add(cardPage);
    		if (position < ballot.getCards().size())
    			numReviewPages++;
    	}
    	
    	return reviewPages;
    }

    /**
     * Makes a simple background (without the sidebar). Used on override pages
     * and the success page.
     * @return the success page background
     */
    protected Background makeSimpleBackground() {
        PsychLayoutPanel frame = new PsychLayoutPanel();

        Label instructionsTitle = new Label("L0", LiteralStrings.Singleton.get(
                "INSTRUCTIONS_TITLE", language));
        instructionsTitle.setCentered(true);
        instructionsTitle.setSize(instructionsTitle.execute(sizeVisitor));
        frame.addTitle(instructionsTitle);
        frame.addSideBar(1);
        frame.addNextButton(nextInfo);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label("L0", LiteralStrings.Singleton.get(
                "INSTRUCTIONS", language), sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        frame.validate();
        frame.pack();

        BufferedImage image = new BufferedImage(WINDOW_WIDTH, WINDOW_HEIGHT,
                BufferedImage.TYPE_INT_RGB);
        Graphics2D graphs = (Graphics2D) image.getGraphics();
        graphs.setColor(Color.WHITE);
        graphs.fillRect(0, 0, WINDOW_WIDTH, WINDOW_HEIGHT);
        graphs.setColor(Color.PINK);
        graphs.fillRect(0, 0, WINDOW_WIDTH, frame.north.getHeight());
        return new Background(getNextLayoutUID(), image);
    }

    //#ifdef NONE_OF_ABOVE
    protected Page makeNoSelectionPage(int target) {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label successTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("NO_SELECTION_TITLE", language));
        successTitle.setBold(true);
        successTitle.setCentered(true);
        successTitle.setSize(successTitle.execute(sizeVisitor));
        frame.addTitle(successTitle);
        frame.remove(frame.west);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("NO_SELECTION", language), sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        Label returnLbl = new Label(getNextLayoutUID(), LiteralStrings.Singleton
                .get("RETURN_RACE", language), sizeVisitor);
        frame.addReturnButton(returnLbl, target);
        
        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(simpleBackground);
        page.setBackgroundLabel(simpleBackground.getUID());

        for (Component c : frame.getAllComponents()) {
            Spacer s = (Spacer) c;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }
    //#endif

    @Override
    protected Page makeSuccessPage() {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label successTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("SUCCESS_TITLE", language));
        successTitle.setBold(true);
        successTitle.setCentered(true);
        successTitle.setSize(successTitle.execute(sizeVisitor));
        frame.addTitle(successTitle);
        frame.remove(frame.west);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("SUCCESS", language), sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(simpleBackground);
        page.setBackgroundLabel(simpleBackground.getUID());

        for (Component c : frame.getAllComponents()) {
            Spacer s = (Spacer) c;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }
    
    @Override
    protected Page makeChallengePage() {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label challengeTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("CHALLENGE_TITLE", language));
        challengeTitle.setBold(true);
        challengeTitle.setCentered(true);
        challengeTitle.setSize(challengeTitle.execute(sizeVisitor));
        frame.addTitle(challengeTitle);
        frame.remove(frame.west);

        Label challengeInstructions = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("CHALLENGE_INSTRUCTIONS",
                        language), sizeVisitor);
        GridBagConstraints c = new GridBagConstraints();
        c.anchor = GridBagConstraints.NORTH;
        c.fill = GridBagConstraints.VERTICAL;
        c.gridy = 1;
        c.gridx = 0;
        c.weightx = 1;
        c.weighty = 1;
        Spacer instspacer = new Spacer(challengeInstructions, frame.north);
        frame.north.add(instspacer, c);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        c = new GridBagConstraints();

        Spacer sp = new Spacer(challengeButton, east);
        east.add(sp, c);
        
        sp = new Spacer(castButton, east);
        c.gridy = 1;
        c.insets = new Insets(50, 0, 0, 0);
        east.add(sp, c);
        
        frame.addAsEastPanel(east);
        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(simpleBackground);
        page.setBackgroundLabel(simpleBackground.getUID());

        for (Component co : frame.getAllComponents()) {
            Spacer s = (Spacer) co;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }
    
    @Override
    protected Page makeResponsePage() {
        PsychLayoutPanel frame = new PsychLayoutPanel();
        Label responseTitle = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("RESPONSE_TITLE", language));
        responseTitle.setBold(true);
        responseTitle.setCentered(true);
        responseTitle.setSize(responseTitle.execute(sizeVisitor));
        frame.addTitle(responseTitle);
        frame.remove(frame.west);

        JPanel east = new JPanel();
        east.setLayout(new GridBagLayout());
        Label instrLabel = new Label(getNextLayoutUID(),
                LiteralStrings.Singleton.get("RESPONSE", language), sizeVisitor);
        Spacer sp = new Spacer(instrLabel, east);
        east.add(sp);
        frame.addAsEastPanel(east);

        frame.validate();
        frame.pack();

        Page page = new Page();
        page.getComponents().add(simpleBackground);
        page.setBackgroundLabel(simpleBackground.getUID());

        for (Component c : frame.getAllComponents()) {
            Spacer s = (Spacer) c;
            s.updatePosition();
            page.getComponents().add(s.getComponent());
        }
        return page;
    }

}
