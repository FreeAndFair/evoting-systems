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

package preptool.model;

import java.awt.Component;
import java.awt.image.BufferedImage;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Stack;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import javax.swing.ImageIcon;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactoryConfigurationError;


import org.w3c.dom.Document;
import org.xml.sax.SAXException;

import preptool.controller.exception.BallotExportException;
import preptool.controller.exception.BallotOpenException;
import preptool.controller.exception.BallotPreviewException;
import preptool.controller.exception.BallotSaveException;
import preptool.model.ballot.ACard;
import preptool.model.ballot.Ballot;
import preptool.model.ballot.ICardFactory;
import preptool.model.ballot.PresidentialRaceCard;
import preptool.model.ballot.PropositionCard;
import preptool.model.ballot.RaceCard;
import preptool.model.ballot.module.AModule;
import preptool.model.language.Language;
import preptool.model.layout.Layout;
import preptool.model.layout.manager.ILayoutManager;
import preptool.model.layout.manager.ILayoutManagerFactory;
import preptool.model.layout.manager.PsychLayoutManager;
import preptool.model.layout.manager.Spacer;
import preptool.view.ProgressInfo;
import preptool.view.View;
import preptool.view.dialog.ProgressDialog;


/**
 * Implementation of the model of the preptool. Contains a Ballot and a
 * LayoutManager.
 * 
 * @author cshaw
 */
public class Model {

    private Ballot ballot;

    private ILayoutManagerFactory managerFactory;

    private ICardFactory[] cardFactories;
    
    private int cardsPerReviewPage = 10;
    private int fontSize = 8;
    private boolean commitChallenge = false;

    /**
     * Creates a new Model with a blank Ballot and using the PsychLayoutManager.
     */
    public Model() {
        newBallot();

        managerFactory = new ILayoutManagerFactory() {
            public ILayoutManager makeLayoutManager(Language language,
            		int numCardsPerReviewPage, int fontSize,
            		boolean commitChallenge) {
                return new PsychLayoutManager( language,
                		numCardsPerReviewPage, fontSize, commitChallenge );
            }
        };

        cardFactories = new ICardFactory[] {
                RaceCard.FACTORY, PresidentialRaceCard.FACTORY,
                PropositionCard.FACTORY
        };
    }

    /**
     * Adds the given card to the ballot
     * 
     * @param newCard
     *            the card to add
     */
    public void addCard(ACard newCard) {
        getBallot().getCards().add( newCard );
    }

    /**
     * Adds the directory to a ZIP file
     */
    private void addDirectoryToZip(ZipOutputStream out, File dir, String path)
            throws IOException {
        byte[] buf = new byte[1024];
        File[] children = dir.listFiles();
        for (File f : children) {
            if (f.isDirectory()) {
                out.putNextEntry( new ZipEntry( path + f.getName() + '/' ) );
                out.closeEntry();
                addDirectoryToZip( out, f, path + f.getName() + '/' );
            }
            else {
                FileInputStream in = new FileInputStream( f );
                out.putNextEntry( new ZipEntry( path + f.getName() ) );

                // Transfer bytes from the file to the ZIP file
                int len;
                while ((len = in.read( buf )) > 0) {
                    out.write( buf, 0, len );
                }

                // Complete the entry
                out.closeEntry();
                in.close();
                f.deleteOnExit();
            }
        }
    }

    /**
     * Checks the ballot for any cards that are missing translations, and then
     * returns a list of Strings with their names so they can be displayed as a
     * list in a dialog
     * 
     * @return list of names of cards missing translations
     */
    public String[] checkTranslations() {
        ArrayList<String> cardsNeeded = new ArrayList<String>();
        for (ACard card : getBallot().getCards()) {
            boolean res = false;
            for (Language lang : getLanguages())
                res |= card.needsTranslation( lang );
            if (res)
                cardsNeeded.add( card.getTitle( getLanguages().get( 0 ) ) );
        }
        return cardsNeeded.toArray( new String[cardsNeeded.size()] );
    }

    /**
     * Deletes the card at index idx from the ballot
     * 
     * @param idx
     *            the index
     */
    public void deleteCard(int idx) {
        getBallot().getCards().remove( idx );
    }

    /**
     * Exports the ballot to VoteBox.
     * 
     * @param view
     *            the main view of the program
     * @param path
     *            the path to export to
     */
    public void export(View view, final String path) {
        export( view, path, null, false );
    }

    /**
     * Exports the ballot to VoteBox
     * 
     * @param view
     *            the main view of the program
     * @param path
     *            the path to export to
     * @param whenDone
     *            Runnable to execute when the export is done
     * @param hideWhenFinished
     *            whether to hide the progress dialog when finished exporting
     */
    public void export(View view, final String path, final Runnable whenDone,
            final boolean hideWhenFinished) {
        final ProgressDialog dialog = new ProgressDialog( view,
                "Exporting Ballot to VoteBox" );

        new Thread() {
            @Override
            public void run() {
                try {
                    ProgressInfo info = dialog.getProgressInfo();
                    dialog.showDialog();

                    int c = 0;
                    info.setNumTasks( getLanguages().size() );
                    for (Language lang : getLanguages()) {
                        final String taskName = "Exporting " + lang.getName()
                                + " Ballot";

                        info.setCurrentTask( taskName, c );
                        info.setProgress( "Laying out Ballot", 0 );
                        ILayoutManager manager = getManagerFactory()
                                .makeLayoutManager( lang, cardsPerReviewPage,
                                		fontSize, commitChallenge  );

                        Layout layout = manager.makeLayout( getBallot() );

                        info.setProgress( "Writing Ballot XML", 0 );
                        Document doc = XMLTools.createDocument();
                        XMLTools.writeXML( getBallot().toXML( doc ), path
                                + "/ballot.xml" );

                        info.setProgress( "Writing Layout XML", 0 );
                        doc = XMLTools.createDocument();
                        XMLTools.writeXML( layout.toXML( doc ), path
                                + "/layout_1_" + lang.getShortName() + ".xml" );

                        manager.renderAllImagesToDisk( layout,
                            path + "/media/", info );
                        BufferedWriter out = new BufferedWriter(
                                new FileWriter( path + "/ballotbox.cfg" ) );
                        out.write( "/ballot.xml" );
                        out.newLine();
                        out.write( "/layout" );
                        out.close();

                        ++c;
                    }
                    info.finished();
                    if (hideWhenFinished)
                        dialog.setVisible( false );
                    if (whenDone != null)
                        whenDone.run();
                }
                catch (TransformerConfigurationException e) {
                    throw new BallotExportException( e );
                }
                catch (IllegalArgumentException e) {
                    throw new BallotExportException( e );
                }
                catch (ParserConfigurationException e) {
                    throw new BallotExportException( e );
                }
                catch (TransformerFactoryConfigurationError e) {
                    throw new BallotExportException( e );
                }
                catch (TransformerException e) {
                    throw new BallotExportException( e );
                }
                catch (IOException e) {
                    throw new BallotExportException( e );
                }
            }
        }.start();
    }

    /**
     * Exports the ballot to VoteBox as a ZIP file.
     * 
     * @param view
     *            the main view of the program
     * @param path
     *            the path to export to
     */
    public void exportAsZip(View view, final String path) {
        exportAsZip( view, path, null, false );
    }

    /**
     * Exports the ballot to VoteBox as a ZIP file
     * 
     * @param view
     *            the main view of the program
     * @param path
     *            the path to export to
     * @param whenDone
     *            Runnable to execute when the export is done
     * @param hideWhenFinished
     *            whether to hide the progress dialog when finished exporting
     */
    public void exportAsZip(View view, final String path,
            final Runnable whenDone, final boolean hideWhenFinished) {
        final ProgressDialog dialog = new ProgressDialog( view,
                "Exporting Ballot to VoteBox" );

        new Thread() {
            @Override
            public void run() {
                try {
                    File tempDir = File.createTempFile( "votebox", "" );
                    tempDir.delete();
                    tempDir.mkdir();

                    String zipFile = path;
                    if (!zipFile.substring( zipFile.length() - 4 ).equals(
                        ".zip" ))
                        zipFile = zipFile + ".zip";

                    ProgressInfo info = dialog.getProgressInfo();
                    dialog.showDialog();

                    int c = 0;
                    info.setNumTasks( getLanguages().size() );
                    for (Language lang : getLanguages()) {
                        final String taskName = "Exporting " + lang.getName()
                                + " Ballot";

                        info.setCurrentTask( taskName, c );
                        info.setProgress( "Laying out Ballot", 0 );
                        ILayoutManager manager = getManagerFactory()
                                .makeLayoutManager( lang, cardsPerReviewPage,
                                		fontSize, commitChallenge );

                        Layout layout = manager.makeLayout( getBallot() );
                        
                        //write to each Card the titleLabelID in the Layout
                        //we start on a different page based on whether or not
                        //there is a language select screen
                        int startPage = getLanguages().size() > 1 ? 2 : 1;
                        for (ACard card : getBallot().getCards()){
                        	//the title label is always the second component, 
                        	//after the background
                        	card.setTitleID(layout.getPages().get(startPage++)
                        			.getComponents().get(1).getUID());
                        }

                        info.setProgress( "Writing Ballot XML", 0 );
                        Document doc = XMLTools.createDocument();
                        XMLTools.writeXML( getBallot().toXML( doc ), tempDir
                                + "/ballot.xml" );

                        info.setProgress( "Writing Layout XML", 0 );
                        doc = XMLTools.createDocument();
                        XMLTools.writeXML( layout.toXML( doc ), tempDir
                                + "/layout_1_" + lang.getShortName() + ".xml" );

                        manager.renderAllImagesToDisk( layout, tempDir
                                + "/media/", info );
                        BufferedWriter out = new BufferedWriter(
                                new FileWriter( tempDir + "/ballotbox.cfg" ) );
                        out.write( "/ballot.xml" );
                        out.newLine();
                        out.write( "/layout" );
                        out.close();

                        ++c;
                    }

                    // Create the ZIP file
                    info.setCurrentTask( "Adding Files to ZIP Archive", c );
                    ZipOutputStream out = new ZipOutputStream(
                            new FileOutputStream( zipFile ) );
                    addDirectoryToZip( out, tempDir, "" );
                    out.close();

                    info.setCurrentTask( "Cleaning up Temporary Files", c );
                    Stack<File> dirStack = new Stack<File>();
                    dirStack.add( tempDir );
                    while (!dirStack.isEmpty()) {
                        File file = dirStack.pop();
                        file.deleteOnExit();
                        File[] children = file.listFiles();
                        for (File f : children) {
                            if (f.isDirectory())
                                dirStack.add( f );
                            else
                                f.deleteOnExit();
                        }
                        if (dirStack.size() > 100)
                            return;
                    }

                    info.finished();
                    if (hideWhenFinished)
                        dialog.setVisible( false );
                    if (whenDone != null)
                        whenDone.run();
                }
                catch (TransformerConfigurationException e) {
                    throw new BallotExportException( e );
                }
                catch (IllegalArgumentException e) {
                    throw new BallotExportException( e );
                }
                catch (ParserConfigurationException e) {
                    throw new BallotExportException( e );
                }
                catch (TransformerFactoryConfigurationError e) {
                    throw new BallotExportException( e );
                }
                catch (TransformerException e) {
                    throw new BallotExportException( e );
                }
                catch (IOException e) {
                    throw new BallotExportException( e );
                }
            }
        }.start();
    }

    /**
     * @return the ballot
     */
    public Ballot getBallot() {
        return ballot;
    }

    /**
     * @return the factories available to create new cards
     */
    public ICardFactory[] getCardFactories() {
        return cardFactories;
    }

    /**
     * Returns the list of modules for the card at the given index
     * 
     * @param idx
     *            the index
     * @return the list of modules
     */
    public ArrayList<AModule> getCardModules(int idx) {
        return getBallot().getCards().get( idx ).getModules();
    }

    /**
     * Returns the title of the card at the given index, in the primary language
     * 
     * @param idx
     *            the index
     * @return the title in the primary language
     */
    public String getCardTitle(int idx) {
        return getBallot().getCards().get( idx ).getTitle(
            getLanguages().get( 0 ) );
    }

    /**
     * Returns a type name of the card at index idx
     * 
     * @param idx
     *            the index
     * @return the type as a string
     */
    public String getCardType(int idx) {
        return getBallot().getCards().get( idx ).getType();
    }

    /**
     * @return the list of languages in the ballot
     */
    public ArrayList<Language> getLanguages() {
        return getBallot().getLanguages();
    }

    /**
     * @return the layout manager
     */
    public ILayoutManagerFactory getManagerFactory() {
        return managerFactory;
    }

    /**
     * @return the number of cards in the ballot
     */
    public int getNumCards() {
        return getBallot().getCards().size();
    }

    /**
     * @return the list of parties in the ballot
     */
    public ArrayList<Party> getParties() {
        return getBallot().getParties();
    }

    /**
     * Moves a card from oldIdx to newIdx in the ballot
     * 
     * @param oldIdx
     *            the old index
     * @param newIdx
     *            the new index
     */
    public void moveCard(int oldIdx, int newIdx) {
        ACard card = getBallot().getCards().remove( oldIdx );
        getBallot().getCards().add( newIdx, card );
    }

    /**
     * Starts a new ballot
     */
    public void newBallot() {
        ballot = new Ballot();
        getBallot().getLanguages().add( Language.getAllLanguages().get( 0 ) );
    }

    /**
     * Opens and loads a ballot from an XML file
     * 
     * @param file
     *            the file to open from
     */
    public void open(String file) {
        try {
            Document doc = XMLTools.readXML( file );
            ballot = Ballot.parseXML( doc.getDocumentElement() );
        }
        catch (ParserConfigurationException e) {
            throw new BallotOpenException( e );
        }
        catch (SAXException e) {
            throw new BallotOpenException( e );
        }
        catch (IOException e) {
            throw new BallotOpenException( e );
        }
    }

    /**
     * Previews the entire ballot in VoteBox, by exporting to a temporary
     * directory and then launching VoteBox
     * 
     * @param view
     *            the main view
     */
    public void previewBallot(final View view) {
        try {
            final File tempDir = File.createTempFile( "votebox", "" );
            tempDir.delete();
            tempDir.mkdir();
            Runnable whenDone = new Runnable() {
                public void run() {
                    // Run in VoteBox
                    votebox.middle.datacollection.DataLogger.init( new File(
                            tempDir, "log" ) );
                    new votebox.middle.driver.Driver(
                            tempDir.getAbsolutePath(),
                            new votebox.middle.view.AWTViewFactory( true, false ), false)
                            .run();

                    // Delete temporary directories
                    Stack<File> dirStack = new Stack<File>();
                    dirStack.add( tempDir );
                    while (!dirStack.isEmpty()) {
                        File file = dirStack.pop();
                        file.deleteOnExit();
                        File[] children = file.listFiles();
                        for (File f : children) {
                            if (f.isDirectory())
                                dirStack.add( f );
                            else
                                f.deleteOnExit();
                        }
                        if (dirStack.size() > 100)
                            return;
                    }
                }
            };
            export( view, tempDir.getAbsolutePath(), whenDone, true );

        }
        catch (IOException e) {
            throw new BallotPreviewException( e );
        }
    }

    /**
     * Renders one or more JPanels of the given card - if there is more than one
     * panel, it is because the card is on multiple pages.<br>
     * All rendering is done in a separate thread.
     * 
     * @param idx
     *            the index of the card to preview
     * @param language
     *            the language to preview it in
     * @return a list of rendered panels that can be displayed
     */
    public ArrayList<JPanel> previewCard(int idx, Language language) {
        final ILayoutManager manager = getManagerFactory().makeLayoutManager(
            language, cardsPerReviewPage, fontSize, commitChallenge );
        final ArrayList<JPanel> panels = manager.makeCardPage( getBallot()
                .getCards().get( idx ) );
        new Thread() {
            public void run() {
                for (JPanel panel : panels) {
                    for (Component comp : panel.getComponents()) {
                        if (comp instanceof Spacer) {
                            final Spacer spacer = (Spacer) comp;
                            final BufferedImage image = spacer.getComponent()
                                    .execute( manager.getImageVisitor(), false );
                            if (image != null) {
                                SwingUtilities.invokeLater( new Runnable() {
                                    public void run() {
                                        spacer.setIcon( new ImageIcon( image ) );
                                    }
                                } );
                            }
                        }
                    }
                }
            }
        }.start();
        return panels;
    }

    /**
     * Saves the ballot as an XML file
     * 
     * @param file
     *            the file to save to
     */
    public void saveAs(String file) {
        try {
            if (!file.substring( file.length() - 4 ).equals( ".bal" ))
                file = file + ".bal";
            Document doc = XMLTools.createDocument();
            XMLTools.writeXML( getBallot().toSaveXML( doc ), file );
        }
        catch (TransformerConfigurationException e) {
            throw new BallotSaveException( e );
        }
        catch (IllegalArgumentException e) {
            throw new BallotSaveException( e );
        }
        catch (ParserConfigurationException e) {
            throw new BallotSaveException( e );
        }
        catch (TransformerFactoryConfigurationError e) {
            throw new BallotSaveException( e );
        }
        catch (TransformerException e) {
            throw new BallotSaveException( e );
        }
    }

    /**
     * Sets the list of languages
     * 
     * @param languages
     *            the new list of languages
     */
    public void setLanguages(ArrayList<Language> languages) {
        getBallot().setLanguages( languages );
    }
    
    /**
     * Sets the properties of the layout
     * 
     * @param numCardsPerReviewPage the number of races shown on one review page
     */
    public void setCardsPerReviewPage(int numCardsPerReviewPage){
    	cardsPerReviewPage = numCardsPerReviewPage;
    }
    
    /**
     * Sets the properties of the layout
     * 
     * @param fontSizeMultiplier the font size multiplier
     */
    public void setFontSize(int fontSizeMultiplier){
    	fontSize = fontSizeMultiplier;
    }
    
    /**
     * Sets the properties of the layout
     * 
     * @param commitChallengeModel whether the ballot will be in Commit-Challenge style
     */
    public void setCommitChallenge(boolean commitChallengeModel){
    	commitChallenge = commitChallengeModel;
    }

    /**
     * @return Number of cards/items found per review page
     */
	public int getCardsPerReviewPage() {
		return cardsPerReviewPage;
	}

	/**
	 * @return Current base font size.
	 */
	public int getBaseFontSize() {
		return fontSize;
	}

}
