package org.scantegrity.common;

import java.awt.image.BufferedImage;
import java.util.TreeMap;
import java.util.Vector;

import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;

import org.scantegrity.common.BallotGeometryMap;
import org.scantegrity.common.Cluster;
import org.scantegrity.common.Prow;
import org.scantegrity.common.ScannedBallot.TypeOfVotes;

public interface ScannedBallotInterface {

	public String getSerial();
	/**
	 * Given a scanned ballot, detects the votes and the serial number
	 * @param img
	 * @throws Exception - if the serial number cannot be properly read
	 */
	public void detect(BufferedImage img) throws Exception;
	/** 
	 * @return the correct marks (only) for the contest that are fully votes
	 */
	public Vector<Cluster> getFullVotes();
	/** 
	 * @return the overvotes that appear on the ballot
	 */	
	public Vector<Cluster> getOverVotes();
	/** 
	 * @return the correct marks (only) for the contest that are undervoted
	 */	
	public Vector<Cluster> getUnderVotes();
	public TreeMap<Integer, TreeMap<Integer, TreeMap<Integer, TypeOfVotes>>> getAllContests();
	/**
	 * @return the scanned ballot in xml format, accepted by the web server for uploading
	 */
	public byte[] toXMLString();
	/**
	 * @return - the streighen image (perfectly aligned)
	 */
	public BufferedImage getPerfectImage();
	/** 
	 * @return the dpi of the scanned image
	 */
	public double getDpi();
	/** 
	 * @return the scanned page
	 */
	public Prow.ChosenPage getSelectedPage();
	public BallotGeometryMap getBallotGeometryMap();
	/**
	 * [T|B]serial space separated marked possitions. If a possition is not marked, -1 is used
	 * @return a one line representation of the scanned ballot
	 */
	public String getCompactRepresentation();
	/** 
	 * @param mailIn if a ballot is mailed in, the other page is marked as scanned
	 * (i.e. the the top page is scanned, bottom is recorded).
	 * This can be done because only the possitions are retained
	 */
	public void setMailIn(boolean mailIn);
	/** 
	 * @return if the ballot commes from a mailed in ballot
	 */
	public boolean isMailIn();
	/** 
	 * @return a scanned ballot in Prow representation
	 */
	public Prow toProw();
	
	/**
	 * @return for each race it returns if the race has not voted at all, undervoted, overvoted or fully voted.
	 */
	public TreeMap<Integer, TypeOfVotes> getRacesCorrectness();
	
	/**
	 * 
	 * @return the question possition that contains a writein vote. If no writein
	 * votes are present, it returns -1
	 * @throws Exception if it cannot be inffered if a writein vote is present or not.
	 * For example when there is a PunchScan ballot, the scanned ballot is already encoded. 
	 */
	public int containsWritein() throws Exception;
	
	public boolean isFullyMarked();
	
	public ElectionSpecification getElectionSpec();
}
