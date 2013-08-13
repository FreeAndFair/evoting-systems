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

package votebox.middle.datacollection;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Observable;
import java.util.Observer;

import auditorium.IAuditoriumParams;
import auditorium.IKeyStore;

import sexpression.ASExpression;
import sexpression.ListExpression;
//#ifdef EVIL
import votebox.middle.datacollection.evil.EvilObserver;
//#endif
import votebox.middle.driver.Driver;
import votebox.middle.view.AWTViewFactory;

/**
 * This is a launcher for the vote system. Use this launcher in order to do
 * human factors type testing.
 * @author Kyle
 */
public class Launcher {

    private static final File SettingsFile = new File("settings");

    /**
     * This is the gui for this launcher.
     */
    private LauncherView _view = null;

    /**
     * This is the votebox that is currently running.
     */
    private Driver _voteBox = null;

    /**
     * Launch the votebox software after doing some brief sanity checking. These
     * checks won't catch everything but they will catch enough problems caused
     * by simple accidents.
     * @param ballotLocation This is the location of the ballot. (zip)
     * @param logDir This is the directory that log files shuld be written out
     *            to. (dir)
     * @param logFilename This is the desired filename for the log file.
     * @param debug Passed to AWTViewFactory to determine windowed/fullscreen mode.
     */
    public void launch(final String ballotLocation, String logDir,
			String logFilename, boolean debug, final String vvpat, final int vvpatWidth,
			final int vvpatHeight, final int printableWidth, final int printableHeight
			//#ifdef EVIL
			, final EvilObserver evilObserver
			//#endif
			) {

		// Unzip the ballot to a temporary directory
		File baldir;
		try {
			baldir = File.createTempFile("ballot", "");
			baldir.delete();
			baldir.mkdirs();
			Driver.unzip(ballotLocation, baldir.getAbsolutePath());
			Driver.deleteRecursivelyOnExit(baldir.getAbsolutePath());
		} catch (IOException e) {
			e.printStackTrace();
			return;
		}
		System.out.println(baldir.getAbsolutePath());

		// Check that ballot location is legit.
		// Check that it's a directory.
		File logdir = new File(logDir);
		File logfile = new File(logdir, logFilename);
		if (!baldir.isDirectory()) {
			_view
					.statusMessage(
							"Supplied 'ballot location' is not a directory.",
							"Please make sure that you select a directory which contains a ballot configuration file and media directory. Do not select a file.");
			return;
		}
		// Check that it has the cfg file.
		if (!Arrays.asList(baldir.list()).contains("ballotbox.cfg")) {
			_view
					.statusMessage(
							"Supplied 'ballot location' does not contain the file 'ballotbox.cfg'",
							"Please specify a valid ballot.zip or ballot directory."
							);
			return;
		}
		// Check that the log directory is actually a directory
		if (!logdir.isDirectory()) {
			_view
					.statusMessage(
							"Supplied 'log directory' is not a directory.",
							"Please make sure that you select a directory\nfor 'log directory' field. Do not select a file.");
			return;
		}
		// Check that the user actually specified a log filename.
		if (logFilename.equals("")) {
			_view.statusMessage("Log Filename blank.",
					"Please specify a log filename.");
			return;
		}
		// Check that the log file does not already exist. If it exists, notify
		// the user that stuff will be appended to the end.
		if (logfile.exists()) {
			// Mangle a name that doesn't exist
			int i = 2;
			String startname = logfile.getName();
			while (logfile.exists())
				logfile = new File(startname + "-" + i++);

			if (!_view.askQuestion("Supplied 'log file' exists",
					"If you choose to continue, event data will be recorded to the file: "
							+ logfile.getName())) return;
		}

		// Set the data logger and launch.
		DataLogger.init(logfile);
		save(ballotLocation, logDir, logFilename);
		_voteBox = null;
		System.gc();
		_voteBox = new Driver(baldir.getAbsolutePath(), new AWTViewFactory(
				debug, false), false);
		final Driver vbcopy = _voteBox;
        
		_view.setRunning(true);
		new Thread(new Runnable() {

			public void run() {
				
				final IAuditoriumParams constants = new IAuditoriumParams(){

					public boolean getAllowUIScaling() { return true; }
					
					public boolean getUseWindowedView() {return true;}
					
					public String getBroadcastAddress() {return null;}

					public boolean getCastBallotEncryptionEnabled() {return false;}

					public String getChallengeBallotFile() {return null;}

					public int getChallengePort() {return 0;}

					public int getDefaultSerialNumber() {return 0;}

					public int getDiscoverPort() {return 0;}

					public int getDiscoverReplyPort() {return 0;}

					public int getDiscoverReplyTimeout() {return 0;}

					public int getDiscoverTimeout() {return 0;}

					public String getEloTouchScreenDevice() {return null;}

					public int getHttpPort() {return 0;}

					public int getJoinTimeout() {return 0;}

					public IKeyStore getKeyStore() {return null;}

					public int getListenPort() {return 0;}

					public String getLogLocation() {return null;}

					public int getPaperHeightForVVPAT() {
						return vvpatHeight;
					}

					public int getPaperWidthForVVPAT() {
						return vvpatWidth;
					}

					public int getPrintableHeightForVVPAT() {
						return printableHeight;
					}

					public int getPrintableWidthForVVPAT() {
						return printableWidth;
					}

					public String getPrinterForVVPAT() {
						return vvpat;
					}

					public String getReportAddress() {return null;}

					public String getRuleFile() {return null;}

					public boolean getUseCommitChallengeModel() {return false;}

					public boolean getUseEloTouchScreen() {return false;}

					public int getViewRestartTimeout() {return 1;}

					public boolean getEnableNIZKs() { return false; }
					
					public boolean getUsePiecemealEncryption() { return false; }

					public boolean getUseSimpleTallyView() { return false; }

					public boolean getUseTableTallyView() { return false; }
				};
				
				//#ifdef EVIL
				vbcopy.registerForReview(evilObserver);
				//#endif
				
		        // Register for the cast ballot event, and "review page encountered" event
				vbcopy.run(new Observer(){
					ListExpression _lastSeenBallot = null;
					
					public void update(Observable o, Object arg){
						//System.out.println("Preparing to print");
						
						Object[] obj = (Object[])arg;
						
						//Do nothing if this is before rendering the screen...
						if(!((Boolean)obj[0]))
							return;
						
						ListExpression ballot = (ListExpression)obj[1];
						
						boolean reject = !ballot.toString().equals(""+_lastSeenBallot); 
						
						try{
							if(reject){
								if(_lastSeenBallot != null)
									Driver.printBallotRejected(constants, new File(ballotLocation));

								Driver.printCommittedBallot(constants, ballot, new File(ballotLocation));
							}
						}catch(Exception e){}
						finally{
							_lastSeenBallot = ballot;
						}
					}
				},

				new Observer() {
					public void update(Observable o, Object arg) {

						//#ifdef EVIL
						// EVIL
						ASExpression ballot = (ASExpression)((Object[])arg)[0];
						System.out.println("Preparing to dump ballot:\n\t"+ballot);
						DataLogger.DumpBallot( ballot );
						//#endif
						
						Driver.printBallotAccepted(constants, new File(ballotLocation));

						vbcopy.getView().nextPage();
					}
				});
				_view.setRunning(true);
			}
		}).start();

	}

    public void kill() {
        _voteBox.kill();
        _view.setRunning(false);
    }

    /**
     * Call this method to run the launcher.
     */
    public void run() {
        _view = new LauncherView(this);
        load();
        _view.setRunning(false);
        _view.setVisible(true);
    }

    /**
     * Load the state of the fields from disk.
     */
    private void load() {
        String ballot, logdir, logfile;
        if (SettingsFile.exists()) {
            try {
                BufferedReader reader = new BufferedReader(new FileReader(
                        SettingsFile));
                logdir = reader.readLine();
                ballot = reader.readLine();
                logfile = reader.readLine();
            } catch (Exception e) {
                return;
            }
            _view.setFields(logdir, ballot, logfile);
        }
    }

    /**
     * Save the state of the fields to disk.
     */
    private void save(String ballot, String logdir, String logfile) {
        try {
            PrintWriter writer = new PrintWriter(new FileWriter(SettingsFile));
            writer.write(logdir + "\n");
            writer.write(ballot + "\n");
            writer.write(logfile + "\n");
            writer.close();
        } catch (Exception e) {
            return;
        }

    }

    public static void main(String[] args) {
        new Launcher().run();
    }
}
