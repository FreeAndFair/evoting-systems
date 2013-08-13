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

package votebox;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Observable;
import java.util.Observer;

import javax.swing.Timer;

import edu.uconn.cse.adder.PublicKey;

import sexpression.*;
import votebox.crypto.*;
import votebox.events.*;
import votebox.middle.*;
import votebox.middle.ballot.Ballot;
import votebox.middle.driver.*;
import votebox.middle.view.*;
import auditorium.*;
import auditorium.Event;

/**
 * This is the top level votebox main class. This class organizes and connects
 * the components of VoteBox, namely:<br>
 * 1) The auditorium network<br>
 * 2) The vote storage backend<br>
 * 3) The votebox "middle" (that is, the link between the voter and the backend,
 * the gui)
 * 
 * @author derrley, cshaw
 */
public class VoteBox {

    private final AuditoriumParams _constants;
    private final IViewFactory _factory;
    private VoteBoxAuditoriumConnector auditorium;
    private Driver currentDriver;
    private IVoteBoxInactiveUI inactiveUI;
    private final int mySerial;
    private boolean connected;
    private boolean voting;
    private boolean override;
    private boolean committedBallot;
    private boolean finishedVoting;
    private int label;
    private Event<Integer> labelChangedEvent;
    private int protectedCount;
    private int publicCount;
    private int numConnections;
    private byte[] nonce;
    private int pageBeforeOverride;
    private Timer killVBTimer;
    private Timer statusTimer;
    
    private File _currentBallotFile;
    
    /**
     * Equivalent to new VoteBox(-1).
     */
    public VoteBox(){
    	this(-1);
    }
    
    /**
     * Constructs a new instance of a persistant VoteBox booth. This
     * implementation runs in the background, on an auditorium network, and
     * waits to receive an authorization before launching the VoteBox middle.
     * For a standalone implementation, see
     * {@link votebox.middle.datacollection.Launcher}.
     * 
     * @param serial
     *            the serial number of the votebox
     */
    public VoteBox(int serial) {
        _constants = new AuditoriumParams("vb.conf");
        
        if(serial != -1)
        	mySerial = serial;
        else
        	mySerial = _constants.getDefaultSerialNumber();
        
        
        if(mySerial == -1)
        	throw new RuntimeException("usage: VoteBox <machineID>");
        
        numConnections = 0;
        labelChangedEvent = new Event<Integer>();
        statusTimer = new Timer(300000, new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (connected) {
                    auditorium.announce(getStatus());
                }
            }
        });

        if (_constants.getViewImplementation().equals("AWT")) {
            // run fullscreen on OSX only
            _factory = new AWTViewFactory(_constants.getUseWindowedView(), _constants.getAllowUIScaling());
        } else if (_constants.getViewImplementation().equals("SDL")) {
        	_factory = new VoteboxSDLViewFactory(_constants);
        }else
            throw new RuntimeException(
                    "Unknown view implementation defined in configuration");
    }

    /**
     * Broadcasts this VoteBox booth's status, and resets the status timer
     */
    public void broadcastStatus() {
        auditorium.announce(getStatus());
        statusTimer.restart();
    }

    /**
     * Returns this booth's label, assigned by a supervisor over auditorium. If
     * unassigned, will return 0.
     * 
     * @return the label
     */
    public int getLabel() {
        return label;
    }

    /**
     * Returns this booth's status as a VoteBoxEvent, used for periodic
     * broadcasts
     * 
     * @return the status
     */
    public VoteBoxEvent getStatus() {
        VoteBoxEvent event;

        int battery = BatteryStatus.read();

        if (voting)
            event = new VoteBoxEvent(mySerial, label, "in-use", battery,
                    protectedCount, publicCount);
        else
            event = new VoteBoxEvent(mySerial, label, "ready", battery,
                    protectedCount, publicCount);
        return event;
    }

    /**
     * Allows the VoteBox inactive UI (what is shown when a user isn't voting)
     * to register for a label changed event, and update itself accordingly
     * 
     * @param obs
     *            the observer
     */
    public void registerForLabelChanged(Observer obs) {
        labelChangedEvent.addObserver(obs);
    }

    /**
     * Launch the VoteBox middle. Registers for events that we would want to
     * know about (such as cast ballot, so we can send the message over
     * auditorium)
     * 
     * @param location
     *            the location on disk of the ballot
     */
    public void run(String location) {
        inactiveUI.setVisible(false);
        currentDriver = new Driver(location, _factory, _constants.getCastBallotEncryptionEnabled());
        voting = true;
        currentDriver.run();

        //If we're using the commit-challenge model, we need to register for the commit & challenge events.
        if(_constants.getUseCommitChallengeModel()){
        	
        	//Listen for challenges ui events.  When received, discard the ballot (as the vote is no longer countable)
        	//   and reply with the random key needed to decrypt this particular vote
        	currentDriver.getView().registerForChallenge(new Observer() {
            	/**
                 * Makes sure that the booth is in a correct state to cast a ballot,
                 * then announce the cast-ballot message (also increment counters)
                 */
                public void update(Observable arg0, Object arg1) {
                    if (!connected)
                        throw new RuntimeException(
                                "Attempted to cast ballot when not connected to any machines");
                    if (!voting || currentDriver == null)
                        throw new RuntimeException(
                                "VoteBox attempted to cast ballot, but was not currently voting");
                    if (finishedVoting)
                        throw new RuntimeException(
                                "This machine has already finished voting, but attempted to vote again");

                    finishedVoting = true;

                    if(!_constants.getEnableNIZKs()){
	                    auditorium.announce(new ChallengeEvent(mySerial,
	                            StringExpression.makeString(nonce),
	                            BallotEncrypter.SINGLETON.getRecentRandom()));
                    }else{
                    	auditorium.announce(new AdderChallengeEvent(mySerial,
                    			StringExpression.makeString(nonce),
                    			BallotEncrypter.SINGLETON.getRecentAdderRandom()));
                    }

                    BallotEncrypter.SINGLETON.clear();
                    
                    //printBallotSpoiled();
                }
            });
        	
        	//Listen for commit ui events.  When received, send out an encrypted vote.
        	currentDriver.getView().registerForCommit(new Observer() {

        		@SuppressWarnings("unchecked")
				public void update(Observable o, Object argTemp) {
        			if (!connected)
        				throw new RuntimeException(
        						"Attempted to cast ballot when not connected to any machines");
        			if (!voting || currentDriver == null)
        				throw new RuntimeException(
        						"VoteBox attempted to cast ballot, but was not currently voting");
        			if (finishedVoting)
        				throw new RuntimeException(
        						"This machine has already finished voting, but attempted to vote again");

                    committedBallot = true;
                    
                    Object[] arg = (Object[])argTemp;
                    
        			// arg1 should be the cast ballot structure, check
        			if (Ballot.BALLOT_PATTERN.match((ASExpression) arg[0]) == NoMatch.SINGLETON)
        				throw new RuntimeException(
        						"Incorrectly expected a cast-ballot");
        			ListExpression ballot = (ListExpression) arg[0];

        			try {
        				if(!_constants.getEnableNIZKs()){
						auditorium.announce(new CommitBallotEvent(mySerial,
								StringExpression.makeString(nonce),
								BallotEncrypter.SINGLETON.encrypt(ballot, _constants.getKeyStore().loadKey("public"))));
        				}else{
        					auditorium.announce(new CommitBallotEvent(mySerial,
        							StringExpression.makeString(nonce),
        							BallotEncrypter.SINGLETON.encryptWithProof(ballot, (List<List<String>>)arg[1], (PublicKey)_constants.getKeyStore().loadAdderKey("public"))));
        				}
						
						//printCommittedBallot(ballot);
					} catch (AuditoriumCryptoException e) {
						Bugout.err("Crypto error trying to commit ballot: "+e.getMessage());
						e.printStackTrace();
					}
        		}
        	});
        	
        	//Listen for cast ui events.
        	//Rather than actually send the ballot out, just send the nonce (which can identify the whole
        	//transaction).
        	//Clean up the encryptor afterwards so as to destroy the random number needed for challenging.
        	currentDriver.getView().registerForCastBallot(new Observer(){

				public void update(Observable o, Object argTemp) {
					if (!connected)
        				throw new RuntimeException(
        						"Attempted to cast ballot when not connected to any machines");
        			if (!voting || currentDriver == null)
        				throw new RuntimeException(
        						"VoteBox attempted to cast ballot, but was not currently voting");
        			if (finishedVoting)
        				throw new RuntimeException(
        						"This machine has already finished voting, but attempted to vote again");

        			finishedVoting = true;
        			++publicCount;
        			++protectedCount;
        			
        			//Object[] arg = (Object[])argTemp;
        			
        			auditorium.announce(new CastCommittedBallotEvent(mySerial,
        					StringExpression.makeString(nonce)));
        			
        			BallotEncrypter.SINGLETON.clear();
        			
        			//printBallotCastConfirmation();
				}
        		
        	});
        	
        	/**
        	 * If we're using piecemeal encryption, we need to listen for each page change.
        	 */
        	if(_constants.getUsePiecemealEncryption()){
        		currentDriver.getView().registerForPageChanged(new Observer(){
        			public void update(Observable o, Object args){
        				List<String> affectedUIDs = (List<String>)args;
        				
        				Map<String, List<ASExpression>> needUpdate = currentDriver.getBallotAdapter().getAffectedRaces(affectedUIDs);
        				
        				for(String uid : needUpdate.keySet()){
        					if(!_constants.getEnableNIZKs()){
        						try{
        							PiecemealBallotEncrypter.SINGELTON.update(uid, needUpdate.get(uid), _constants.getKeyStore().loadKey("public"));
        						}catch(AuditoriumCryptoException e){
        							throw new RuntimeException(e);
        						}
        					}else{
        						List<String> raceGroup = currentDriver.getBallotAdapter().getRaceGroupContaining(needUpdate.get(uid));
        						PiecemealBallotEncrypter.SINGELTON.adderUpdate(uid, needUpdate.get(uid), raceGroup, (PublicKey)_constants.getKeyStore().loadAdderKey("public"));
        					}
        				}
        			}
        		});
        	}
        }else{
        	//If we're not using the challenge-commit model, we still need to handle "cast" ui events.
        	//Here we role the commit triggered encryption in with casting (provided encryption is enabled).
        	currentDriver.getView().registerForCastBallot(new Observer() {
        		/**
        		 * Makes sure that the booth is in a correct state to cast a ballot,
        		 * then announce the cast-ballot message (also increment counters)
        		 */
        		@SuppressWarnings("unchecked")
				public void update(Observable o, Object argTemp) {
        			if (!connected)
        				throw new RuntimeException(
        						"Attempted to cast ballot when not connected to any machines");
        			if (!voting || currentDriver == null)
        				throw new RuntimeException(
        						"VoteBox attempted to cast ballot, but was not currently voting");
        			if (finishedVoting)
        				throw new RuntimeException(
        						"This machine has already finished voting, but attempted to vote again");

        			finishedVoting = true;
        			++publicCount;
        			++protectedCount;

        			Object[] arg = (Object[])argTemp;
        			
        			//If we are not using encryption use the plain old CastBallotEvent
        			if(!_constants.getCastBallotEncryptionEnabled()){
        				auditorium.announce(new CastBallotEvent(mySerial,
        						StringExpression.makeString(nonce),
        						(ASExpression)arg[0]));
        			}else{
        				//Else, use the EncryptedCastBallotEvent with a properly encrypted ballot
        				try{
        					if(!VoteBox.this._constants.getEnableNIZKs()){
        						BallotEncrypter.SINGLETON.encrypt((ListExpression)arg[0], _constants.getKeyStore().loadKey("public"));

        						auditorium.announce(new EncryptedCastBallotEvent(mySerial,
        								StringExpression.makeString(nonce),
        								BallotEncrypter.SINGLETON.getRecentEncryptedBallot()));
        					}else{
        						BallotEncrypter.SINGLETON.encryptWithProof((ListExpression)arg[0], (List<List<String>>)arg[1], (PublicKey)_constants.getKeyStore().loadAdderKey("public"));
        						
        						auditorium.announce(new EncryptedCastBallotWithNIZKsEvent(mySerial,
        								StringExpression.makeString(nonce),
        								BallotEncrypter.SINGLETON.getRecentEncryptedBallot()));
        					}//if
        				} catch (AuditoriumCryptoException e) {
							System.err.println("Encryption Error: "+e.getMessage());
						}
        			}

        			BallotEncrypter.SINGLETON.clear();
        			
        			//printCommittedBallot((ListExpression)arg);
        			//printBallotCastConfirmation();
        		}
        	});
        }//if
        
        currentDriver.getView().registerForOverrideCancelConfirm(
                new Observer() {
                    /**
                     * Kill the VB runtime, and announce the confirm message
                     */
                    public void update(Observable o, Object arg) {
                        if (voting && override && !finishedVoting
                                && currentDriver != null) {
                            auditorium.announce(new OverrideCancelConfirmEvent(
                                    mySerial, nonce));
                            currentDriver.kill();
                            currentDriver = null;
                            nonce = null;
                            voting = false;
                            override = false;
                            broadcastStatus();
                            inactiveUI.setVisible(true);
                            
                            //printBallotSpoiled();
                        } else
                            throw new RuntimeException(
                                    "Received an override-cancel-confirm event at the incorrect time");
                    }
                });
        
        currentDriver.getView().registerForOverrideCancelDeny(new Observer() {
            /**
             * Announce the deny message, and return to the page the voter was
             * previously on
             */
            public void update(Observable o, Object arg) {
                if (voting && override && !finishedVoting
                        && currentDriver != null) {
                    auditorium.announce(new OverrideCancelDenyEvent(mySerial,
                            nonce));
                    override = false;
                    currentDriver.getView().drawPage(pageBeforeOverride);
                } else
                    throw new RuntimeException(
                            "Received an override-cancel-deny event at the incorrect time");
            }
        });
        
        currentDriver.getView().registerForOverrideCastConfirm(new Observer() {
            /**
             * Increment counters, and send the ballot in the confirm message.
             * Also kill votebox and show the inactive UI
             */
            public void update(Observable o, Object arg) {
                if (voting && override && !finishedVoting
                        && currentDriver != null) {
                    ++publicCount;
                    ++protectedCount;
                    byte[] ballot = ((ASExpression) arg).toVerbatim();
                    auditorium.announce(new OverrideCastConfirmEvent(mySerial,
                            nonce, ballot));
                    currentDriver.kill();
                    currentDriver = null;
                    nonce = null;
                    voting = false;
                    override = false;
                    broadcastStatus();
                    inactiveUI.setVisible(true);
                    
                    //printBallotCastConfirmation();
                } else
                    throw new RuntimeException(
                            "Received an override-cast-confirm event at the incorrect time");
            }
        });
        
        currentDriver.getView().registerForOverrideCastDeny(new Observer() {
            /**
             * Announce the deny message, and return to the page the voter was
             * previously on
             */
            public void update(Observable o, Object arg) {
                if (voting && override && !finishedVoting
                        && currentDriver != null) {
                    auditorium.announce(new OverrideCastDenyEvent(mySerial,
                            nonce));
                    override = false;
                    currentDriver.getView().drawPage(pageBeforeOverride);
                } else
                    throw new RuntimeException(
                            "Received an override-cast-deny event at the incorrect time");
            }
        });
    }
    
    /**
     * If a VVPAT is connected,
     *   print a message indicating that this ballot is "spoiled" and will not be counted."
     */
    /*protected void printBallotSpoiled() {
    	
    	//TODO: Change this to use prerendered images (pulled from ballot, probably) rather than bringing Java font rendering code into
    	//      VoteBox
		Printable spoiled = new Printable(){
			public int print(Graphics graphics, PageFormat pageFormat, int pageIndex) throws PrinterException {
				if(pageIndex != 0) return Printable.NO_SUCH_PAGE;
				
				String text = "BALLOT SPOILED";
				FontRenderContext context = new FontRenderContext(new AffineTransform(), false, true);
				
				Rectangle2D bounds = graphics.getFont().getStringBounds(text, context);
				
				while(bounds.getWidth() < pageFormat.getImageableWidth()){
					text = "*" + text+ "*";
					bounds = graphics.getFont().getStringBounds(text, context);
				}
				
				graphics.drawString(text, (int)pageFormat.getImageableX(), (int)bounds.getHeight());
				
				return Printable.PAGE_EXISTS;
			}
		};
		
		printOnVVPAT(spoiled);
	}*/

	/**
     * If a VVPAT is connected,
     *   print a "confirmation" of the ballot being counted.
     */
    /*protected void printBallotCastConfirmation() {
    	//TODO: Make this use prerendered elements instead of Font
    	Printable confirmed = new Printable(){
			public int print(Graphics graphics, PageFormat pageFormat, int pageIndex) throws PrinterException {
				if(pageIndex != 0) return Printable.NO_SUCH_PAGE;
				
				String text = "--BALLOT CAST--";
				FontRenderContext context = new FontRenderContext(new AffineTransform(), false, true);
				
				Rectangle2D bounds = graphics.getFont().getStringBounds(text, context);
				
				int x = (int)(pageFormat.getImageableWidth()/2  - bounds.getWidth() / 2);
				
				graphics.drawString(text, x + (int)pageFormat.getImageableX(), (int)bounds.getHeight());
				
				return Printable.PAGE_EXISTS;
			}
		};
		
		printOnVVPAT(confirmed);
	}*/

    /**
     * If a VVPAT is connected,
     *   print the voter's choices.
     *   
     * @param ballot - the choices to print, in the form ((race-id choice) ...)
     */
	/*protected void printCommittedBallot(ListExpression ballot) {
		final Map<String, Image> choiceToImage = BallotImageHelper.loadImagesForVVPAT(_currentBallotFile);
		
		final List<String> choices = new ArrayList<String>();
		for(int i = 0; i < ballot.size(); i++){
			ListExpression choice = (ListExpression)ballot.get(i);
			if(choice.get(1).toString().equals("1"))
				choices.add(choice.get(0).toString());
		}
		
		int totalSize = 0;
		for(int i = 0; i < choices.size(); i++)
			totalSize += choiceToImage.get(choices.get(i)).getHeight(null);
		
		final int fTotalSize = totalSize;
		
		Printable printedBallot = new Printable(){

			public int print(Graphics graphics, PageFormat pageFormat, int pageIndex) throws PrinterException {
				int numPages = fTotalSize / (int)pageFormat.getImageableHeight();
				if(fTotalSize % (int)pageFormat.getImageableHeight() != 0)
					numPages++;
				
				if(pageIndex >= numPages)
					return Printable.NO_SUCH_PAGE;
				
				int choiceIndex = 0;
				int totalSize = 0;
				while(pageIndex != 0){
					totalSize += choiceToImage.get(choices.get(choiceIndex)).getHeight(null);
					
					if(totalSize > pageFormat.getImageableHeight()){
						totalSize = 0;
						choiceIndex--;
						pageIndex--;
					}
					
					choiceIndex++;
				}
				
				totalSize = 0;
				while(totalSize < pageFormat.getImageableHeight() && choiceIndex < choices.size()){
					Image img = choiceToImage.get(choices.get(choiceIndex));
					
					graphics.drawImage(img,
							(int)pageFormat.getImageableX(),
							totalSize,
							null);
					
					totalSize += img.getHeight(null);
					choiceIndex++;
				}
				
				return Printable.PAGE_EXISTS;
			}
			
		};
		
		printOnVVPAT(printedBallot);
	}*/

	/**
	 * Prints onto the attached VVPAT printer, if possible.
	 * @param print - the Printable to print.
	 */
	/*protected void printOnVVPAT(Printable toPrint){
		//VVPAT not ready
		if(_constants.getPrinterForVVPAT().equals("")) return;
		
		PrintService[] printers = PrinterJob.lookupPrintServices();
		
		PrintService vvpat = null;
		
		for(PrintService printer : printers){
			PrinterName name = printer.getAttribute(PrinterName.class);
			if(name.getValue().equals(_constants.getPrinterForVVPAT())){
				vvpat = printer;
				break;
			}//if
		}//for
		
		if(vvpat == null){
			Bugout.msg("VVPAT is configured, but not detected as ready.");
			return;
		}
		
		PrinterJob job = PrinterJob.getPrinterJob();
		
		try {
			job.setPrintService(vvpat);
		} catch (PrinterException e) {
			Bugout.err("VVPAT printing failed: "+e.getMessage());
			return;
		}
		
		Paper paper = new Paper();
		paper.setSize(_constants.getPaperWidthForVVPAT(), _constants.getPaperHeightForVVPAT());
		
		int imageableWidth = _constants.getPrintableWidthForVVPAT();
		int imageableHeight = _constants.getPrintableHeightForVVPAT();
		
		int leftInset = (_constants.getPaperWidthForVVPAT() - _constants.getPrintableWidthForVVPAT()) / 2;
		int topInset = (_constants.getPaperHeightForVVPAT() - _constants.getPrintableHeightForVVPAT()) / 2;
		
		paper.setImageableArea(leftInset, topInset, imageableWidth, imageableHeight);
		PageFormat pageFormat = new PageFormat();
		pageFormat.setPaper(paper);
		
		job.setPrintable(toPrint, pageFormat);
		
		try {
			job.print();
		} catch (PrinterException e) {
			Bugout.err("VVPAT printing failed: "+e.getMessage());
			return;
		}
	}*/
	
	/**
     * Starts Auditorium, registers the listener, and connects to the network.
     */
    public void start() {
        if(_constants.getViewImplementation().equals("SDL"))
        	inactiveUI = new VoteBoxSDLInactiveUI(this, _constants);
        else
        	inactiveUI = new VoteBoxInactiveUI(this);
        
        inactiveUI.setVisible(true);

        try {
            auditorium = new VoteBoxAuditoriumConnector(mySerial,
            		_constants,
                    ActivatedEvent.getMatcher(), AssignLabelEvent.getMatcher(),
                    AuthorizedToCastEvent.getMatcher(), BallotReceivedEvent.getMatcher(),
                    OverrideCancelEvent.getMatcher(), OverrideCastEvent.getMatcher(),
                    PollsOpenQEvent.getMatcher(), BallotCountedEvent.getMatcher(),
                    ChallengeEvent.getMatcher(), ChallengeResponseEvent.getMatcher(),
                    AuthorizedToCastWithNIZKsEvent.getMatcher());
        } catch (NetworkException e1) {
        	//NetworkException represents a recoverable error
        	//  so just note it and continue
            System.out.println("Recoverable error occured: "+e1.getMessage());
            e1.printStackTrace(System.err);
        }

        auditorium.addListener(new VoteBoxEventListener() {
			public void ballotCounted(BallotCountedEvent e){
        		if (e.getNode() == mySerial
                        && Arrays.equals(e.getNonce(), nonce)) {
                    if (!finishedVoting)
                        throw new RuntimeException(
                                "Someone said the ballot was counted, but this machine hasn't finished voting yet");
        		
                    if(!_constants.getUseCommitChallengeModel()){
                    	Bugout.err("Received BallotCounted message while not in Challenge-Commit mode!");
                    	return;
                    }

                    currentDriver.getView().nextPage();
                    nonce = null;
                    voting = false;
                    finishedVoting = false;
                    committedBallot = false;
                    broadcastStatus();
                    killVBTimer = new Timer(_constants.getViewRestartTimeout(), new ActionListener() {
                    	public void actionPerformed(ActionEvent arg0) {
                    		currentDriver.kill();
                    		currentDriver = null;
                    		inactiveUI.setVisible(true);
                    		killVBTimer = null;
                    	};
                    });
                    killVBTimer.setRepeats(false);
                    killVBTimer.start();
        		}//if
        	}
        	
            /**
             * Handler for the activated message. Look to see if this VoteBox's
             * status exists (and is correct), and if not, broadcast its status
             */
            public void activated(ActivatedEvent e) {
                boolean found = false;
                for (StatusEvent ae : e.getStatuses()) {
                    if (ae.getNode() == mySerial) {
                        VoteBoxEvent ve = (VoteBoxEvent) ae.getStatus();
                        VoteBoxEvent status = getStatus();
                        if (!ve.getStatus().equals(status.getStatus())
                                || ve.getBattery() != status.getBattery()
                                || ve.getLabel() != status.getLabel()
                                || ve.getProtectedCount() != status
                                        .getProtectedCount()
                                || ve.getPublicCount() != status
                                        .getPublicCount())
                            broadcastStatus();
                        found = true;
                    }
                }
                if (!found) broadcastStatus();
            }

            /**
             * Handler for the assign-label message. If it is referring to this
             * booth, set the label.
             */
            public void assignLabel(AssignLabelEvent e) {
                if (e.getNode() == mySerial){
                	label = e.getLabel();
                	System.out.println("\tNew Label: "+label);
                }//if
                
                labelChangedEvent.notify(label);
            }

            /**
             * Handler for the authorized-to-cast message. If it is for this
             * booth, and it is not already voting, unzip the ballot and fire
             * the VoteBox runtime. Also announce the new status.
             */
            public void authorizedToCast(AuthorizedToCastEvent e) {
                if (e.getNode() == mySerial) {
                    if (voting || currentDriver != null && killVBTimer == null)
                        throw new RuntimeException(
                                "VoteBox was authorized-to-cast, but was already voting");

                    // If last VB runtime is on thank you screen and counting
                    // down to when it disappears, kill it prematurely without
                    // showing inactive UI
                    if (killVBTimer != null && currentDriver != null) {
                        killVBTimer.stop();
                        killVBTimer = null;
                        currentDriver.kill();
                        currentDriver = null;
                    }

                    nonce = e.getNonce();

                    //Current working directory
                    File path = new File(System.getProperty("user.dir"));
                    path = new File(path, "tmp");
                    path = new File(path, "ballots");
                    path = new File(path, "ballot" + protectedCount);
                    path.mkdirs();
                    
                    try {
                    	_currentBallotFile = new File(path, "ballot.zip");
                    	
                        FileOutputStream fout = new FileOutputStream(_currentBallotFile);
                        byte[] ballot = e.getBallot();
                        fout.write(ballot);
                        
                        Driver.unzip(new File(path, "ballot.zip").getAbsolutePath(), new File(path, "data").getAbsolutePath());
                        Driver.deleteRecursivelyOnExit(path.getAbsolutePath());

                        run(new File(path, "data").getAbsolutePath());
                        broadcastStatus();
                    } catch (IOException e1) {
                        throw new RuntimeException(e1);
                    }
                }
            }

            /**
             * Handler for the ballot-received message. Show the next page on
             * the VB runtime (the thank you screen), and start a timer that
             * kills the runtime after a set amount of time (5 seconds), and
             * then shows the inactive screen. Also responds with its status.
             */
            public void ballotReceived(BallotReceivedEvent e) {
                if (e.getNode() == mySerial
                        && Arrays.equals(e.getNonce(), nonce)) {
                    if (!committedBallot && _constants.getUseCommitChallengeModel())
                        throw new RuntimeException(
                                "Someone said the ballot was received, but this machine hasn't committed it yet. Maybe the supervisor is misconfigured (not using challenge-commit model)?");
                    
                    if(!finishedVoting && !_constants.getUseCommitChallengeModel())
                    	throw new RuntimeException(
                    			"Someone said the ballot was received, but this machine hasn't finished voting yet");
                    
                    currentDriver.getView().nextPage();
                    if(!_constants.getUseCommitChallengeModel()){
                    	nonce = null;
                    	voting = false;
                    	finishedVoting = false;
                    	committedBallot = false;
                    	broadcastStatus();
                    	killVBTimer = new Timer(_constants.getViewRestartTimeout(), new ActionListener() {
                    		public void actionPerformed(ActionEvent arg0) {
                    			currentDriver.kill();
                    			currentDriver = null;
                    			inactiveUI.setVisible(true);
                    			killVBTimer = null;
                    		};
                    	});
                    	killVBTimer.setRepeats(false);
                    	killVBTimer.start();
                    }//if
                }
            }

            public void castBallot(CastBallotEvent e) {
                // NO-OP
            }

            /**
             * Increment the number of connections
             */
            public void joined(JoinEvent e) {
                ++numConnections;
                connected = true;
            }

            public void lastPollsOpen(LastPollsOpenEvent e) {
                // NO-OP
            }

            /**
             * Decrement the number of connections
             */
            public void left(LeaveEvent e) {
                --numConnections;
                if (numConnections == 0) connected = false;
            }

            /**
             * Handler for the override-cancel message. If it is referring to
             * this booth, and it is in a state that it can be overridden, send
             * the runtime to the proper override page and record the page the
             * user was previously on.
             */
            public void overrideCancel(OverrideCancelEvent e) {
                if (mySerial == e.getNode()
                        && Arrays.equals(e.getNonce(), nonce)) {
                    try {
                        if (voting && !finishedVoting && currentDriver != null) {
                            int page = currentDriver.getView().overrideCancel();
                            if (!override) {
                                pageBeforeOverride = page;
                                override = true;
                            }
                        } else
                            throw new RuntimeException(
                                    "Received an override-cancel message when the user wasn't voting");
                    } catch (IncorrectTypeException e1) {
                        Bugout.err("Incorrect type in overrideCancel handler");
                    }
                }
            }

            public void overrideCancelConfirm(OverrideCancelConfirmEvent e) {
                // NO-OP
            }

            public void overrideCancelDeny(OverrideCancelDenyEvent e) {
                // NO-OP
            }

            /**
             * Handler for the override-cast message. If it is referring to this
             * booth, and it is in a state that it can be overridden, send the
             * runtime to the proper override page and record the page the user
             * was previously on.
             */
            public void overrideCast(OverrideCastEvent e) {
                try {
                    if (voting && !finishedVoting && currentDriver != null) {
                        int page = currentDriver.getView().overrideCast();
                        if (!override) {
                            pageBeforeOverride = page;
                            override = true;
                        }
                    } else
                        throw new RuntimeException(
                                "Received an override-cast message when the user wasn't voting");
                } catch (IncorrectTypeException e1) {
                	//We don't want to bail once VoteBox is up and running,
                	//  so report and continue in this case
                    System.out.println("Incorrect type received in overrideCast event: "+e1.getMessage());
                    e1.printStackTrace(System.err);
                }
            }

            public void overrideCastConfirm(OverrideCastConfirmEvent e) {
                // NO-OP
            }

            public void overrideCastDeny(OverrideCastDenyEvent e) {
                // NO-OP
            }

            public void pollsClosed(PollsClosedEvent e) {
                // NO-OP
            }

            public void pollsOpen(PollsOpenEvent e) {
                // NO-OP
            }

            /**
             * Handler for the polls-open? event. Searches the machine's log,
             * and replies with a last-polls-open message if an appropriate
             * polls-open message is found.
             */
            public void pollsOpenQ(PollsOpenQEvent e) {
                if (e.getSerial() != mySerial) {
                    // TODO: Search the log and extract an appropriate
                    // polls-open message

                    ASExpression res = null;
                    if (res != null && res != NoMatch.SINGLETON) {
                        VoteBoxEventMatcher matcher = new VoteBoxEventMatcher(
                                PollsOpenEvent.getMatcher());
                        PollsOpenEvent event = (PollsOpenEvent) matcher.match(
                                0, res);
                        if (event != null
                                && event.getKeyword().equals(e.getKeyword()))
                            auditorium.announce(new LastPollsOpenEvent(
                                    mySerial, event));
                    }
                }
            }

            public void supervisor(SupervisorEvent e) {
                // NO-OP
            }

            public void votebox(VoteBoxEvent e) {
                // NO-OP
            }

            public void commitBallot(CommitBallotEvent e) {
                // NO-OP

            }

            public void challenge(ChallengeEvent e) {
            	if(!_constants.getUseCommitChallengeModel()){
            		Bugout.err("Received Challenge while not using Challenge-Commit model");
            		return;
            	}//if
            	
            	if (e.getSerial() == mySerial
                        && Arrays.equals(e.getNonce().toVerbatim(), nonce)) {
                    if (!finishedVoting)
                        throw new RuntimeException(
                                "Someone said this ballot was challenge, but this machine hasn't finished voting yet");

                    broadcastStatus();
                    
            	}//if

            }
            
            public void challengeResponse(ChallengeResponseEvent e) {
            	if(!_constants.getUseCommitChallengeModel()){
            		Bugout.err("Received Challenge Response while not using Challenge-Commit model");
            		return;
            	}//if

            	if (e.getNode() == mySerial
                        && e.getNonce().equals(StringExpression.makeString(nonce))) {
                    if (!finishedVoting)
                        throw new RuntimeException(
                                "Someone said this ballot was challenge, but this machine hasn't finished voting yet");
                    currentDriver.getView().nextPage();
                    nonce = null;
                    voting = false;
                    finishedVoting = false;
                    committedBallot = false;
                    broadcastStatus();
                    killVBTimer = new Timer(_constants.getViewRestartTimeout(), new ActionListener() {
                    	public void actionPerformed(ActionEvent arg0) {
                    		currentDriver.kill();
                    		currentDriver = null;
                    		inactiveUI.setVisible(true);
                    		killVBTimer = null;
                    	};
                    });
                    killVBTimer.setRepeats(false);
                    killVBTimer.start();
            	}//if

            }

        });

        try {
            auditorium.connect();
            auditorium.announce(getStatus());
        }
        catch (NetworkException e1) {
            throw new RuntimeException(e1);
        }

        statusTimer.start();
    }

    /**
     * Main entry point into the program. If an argument is given, it will be
     * the serial number, otherwise VoteBox will load a serial from its config file.
     * 
     * @param args
     */
    public static void main(String[] args) {
        if (args.length == 1)
            new VoteBox(Integer.parseInt(args[0])).start();
        else
        	//Tell VoteBox to refer to its config file for the serial number
            new VoteBox().start();
    }
}
