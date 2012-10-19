/*
 * @(#)Ballot.java.java
 *  
 * Copyright (C) 2008-2009 Scantegrity Project
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package org.scantegrity.common;

import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Map;
import java.util.TreeMap;
import java.util.Vector;

import javax.imageio.ImageIO;

import org.apache.commons.codec.binary.Base64;


/**
 * Ballot is used for counting the final tally at the end of the day and for
 * storing results so the central system can use them. It must store the
 * ID read by the scanner, the contest IDs and the Ballot Style IDs (which lets
 * us know which contests are on each ballot). 
 * 
 * Notes are stored to indicate if there's a problem with the ballot and how the
 * system resolved that problem, e.g. "This ballot has 2 candidates in Rank 2 on
 * Contest 3, Tally method permits this, left alone," or "No vote for contest 
 * 1." 
 * 
 * This is raw ballot data, not result data. It should not be published 
 * because of pattern marking (italian) attacks. Instead, contest-level 
 * selections should be stored and published.
 * 
 * @author Richard Carback
 *
 */
public class Ballot
{
	/** TODO: Notes should be moved to the published object. */
	
	private Integer c_id;
	private Integer c_ballotStyleID;
	private Integer c_scannerId = -1;
	private Map<Integer, Integer[][]> c_ballotData;
	private boolean c_counted;
	private Vector<String> c_notes;
	private String c_ballotImage; //image saved when a voting error has occurred
	private TreeMap<Integer, Vector<String>> c_errorContests; // the contest ids with errors and the errors that occurred. 
	
	/* Write-in Support */
	//Rectangle clippings of write-in ballot location.  Maps contest ID to map of write-in candidate IDs to images
	private TreeMap<Integer, TreeMap<Integer, String>> c_writeIns = null;
	
	/**
	 * Default Constructor, creates invalid ballot.
	 */
	public Ballot() 
	{
		this (-1, -1, null);
	}

	/**
	 * Creates a new ballot.
	 * @param p_id the ID of the ballot.
	 * @param p_styleID tye style type.
	 * @param p_contestData the actual data on the ballot.
	 */
	public Ballot(Integer p_id, Integer p_styleID, 
					Map<Integer, Integer[][]> p_contestData) 
	{
		c_id = p_id;
		c_ballotStyleID = p_styleID;
		c_ballotData = p_contestData;
		c_notes = new Vector<String>();
		c_counted = true;
	}

	/**
	 * Does this ballot contain results for the given contest?
	 * @param p_contestID
	 * @return true if the contest exists in this ballot, false otherwise.
	 */
	public boolean hasContest(Integer p_contestID) 
	{
		return (c_ballotData.containsKey(p_contestID) && c_counted);
	}
	
	/**
	 * Get results for given contest.
	 * @param p_contestID
	 * @return true if the contest exists in this ballot, false otherwise.
	 */
	public Integer[][] getContestData(Integer p_contestID) 
	{
		if (c_counted) return c_ballotData.get(p_contestID);
		else return null;
	}
	
	/**
	 * @return the id
	 */
	public Integer getId()
	{
		return c_id;
	}

	/**
	 * @param p_id the id to set
	 */
	public void setId(Integer p_id)
	{
		c_id = p_id;
	}

	/**
	 * @return the ballotStyleID
	 */
	public Integer getBallotStyleID()
	{
		return c_ballotStyleID;
	}

	/**
	 * @param p_ballotStyleID the ballotStyleID to set
	 */
	public void setBallotStyleID(Integer p_ballotStyleID)
	{
		c_ballotStyleID = p_ballotStyleID;
	}

	/**
	 * @param scannerId the scannerId to set
	 */
	public void setScannerId(Integer scannerId) {
		c_scannerId = scannerId;
	}

	/**
	 * @return the scannerId
	 */
	public Integer getScannerId() {
		return c_scannerId;
	}

	/**
	 * @return the ballotData
	 */
	public Map<Integer, Integer[][]> getBallotData()
	{
		return c_ballotData;
	}

	/**
	 * @param p_ballotData the ballotData to set
	 */
	public void setBallotData(Map<Integer, Integer[][]> p_ballotData)
	{
		c_ballotData = p_ballotData;
	}

	/**
	 * @param counted the counted to set
	 */
	public void setCounted(boolean counted)
	{
		c_counted = counted;
	}

	/**
	 * @return the counted
	 */
	public boolean isCounted()
	{
		return c_counted;
	}

	/**
	 * @return the notes
	 */
	public Vector<String> getNotes()
	{
		return c_notes;
	}

	/**
	 * @param p_notes the notes to set
	 */
	public void setNotes(Vector<String> p_notes)
	{
		c_notes = p_notes;
	}

	/**
	 * Add note to list.
	 * @param p_note
	 */
	public void addNote(String p_note) {
		c_notes.add(p_note);
	}
	
	/**
	 * This is really weak, that's on purpose!
	 * @param l_rhs
	 * @return
	 */
	public boolean equals(Object l_rhs)
	{
		if (l_rhs instanceof Ballot) 
		{
			if (((Ballot)l_rhs).getId().equals(c_id))
			{
				return true;
			}
		}
		return false;	
	}

	/**
	 * @param writeIns the writeIns to set
	 */
	public void setWriteIns(TreeMap<Integer, TreeMap<Integer, String>> writeIns) 
	{
		c_writeIns = writeIns;
	}

	/**
	 * @return the writeIns
	 */
	public TreeMap<Integer, TreeMap<Integer, String>> getWriteIns() 
	{
		return c_writeIns;
	}
	
	/**
	 * Add a write-in Image to the ballot.
	 * 
	 * @param p_contestId
	 * @param p_contestantId
	 * @param p_img
	 */
	public void addWriteIn(int p_contestId, int p_contestantId, 
							BufferedImage p_img)
	{
		//Ignore null images.
		if (p_img == null) return;
		//Create write-in object
		if (c_writeIns == null)
		{
			c_writeIns = new TreeMap<Integer, TreeMap<Integer, String>>();
		}
		//Add an entry for this contest, if necessary.
		if (!c_writeIns.containsKey(p_contestId))
		{
			c_writeIns.put(p_contestId, new TreeMap<Integer, String>());
		}
		//Remove duplicates
		if (!c_writeIns.get(p_contestId).containsKey(p_contestantId))
		{
			c_writeIns.get(p_contestId).remove(p_contestantId);
		}
		
		//Get bytestream
		ByteArrayOutputStream l_baos = new ByteArrayOutputStream();
        try {
        	ImageIO.write(p_img, "png", l_baos);
        } catch (IOException e) {
        	return;
        }	
 		//UUEncode
 		Base64 l_enc = new Base64();
	 	c_writeIns.get(p_contestId).put(p_contestantId, 
 									l_enc.encodeToString(l_baos.toByteArray())); 
	}
	
	/**
	 * Get all the write in Images.
	 * 
	 * @return
	 */
	public TreeMap<Integer, TreeMap<Integer, BufferedImage>> getWriteInImgs()
	{
		if (c_writeIns == null) return null;
		
		TreeMap<Integer, TreeMap<Integer, BufferedImage>> l_res;
		l_res = new TreeMap<Integer, TreeMap<Integer,BufferedImage>>();
		//For each contestId
		for (Integer l_contestId : c_writeIns.keySet())
		{
			//for each contestantId..
			l_res.put(l_contestId, new TreeMap<Integer, BufferedImage>());
			for (Integer l_contestantId : c_writeIns.get(l_contestId).keySet())
			{
				//Add the image to the list.
				l_res.get(l_contestId).put(l_contestantId, 
							getWriteInImg(l_contestId, l_contestantId));
			}
		}
		
		return l_res;
	}
	
	/**
	 * Get the BufferedImage for a specific contest and candidate.
	 * 
	 * @param p_contestId - the contest ID
	 * @param p_contestantId - the contestant ID
	 * @return
	 */
	public BufferedImage getWriteInImg(int p_contestId, int p_contestantId)
	{
		if (c_writeIns == null) return null;
		
		BufferedImage l_img = null;
		//If we can find it.. decode it.
		if (c_writeIns.containsKey(p_contestId)) 
		{
			if (c_writeIns.get(p_contestId).containsKey(p_contestantId))
			{
				String l_str = c_writeIns.get(p_contestId).get(p_contestantId);
				Base64 l_dec = new Base64();
				//Decode and read in the image.
				try {
					byte[] l_bais = l_dec.decode(l_str);
		            if (l_bais != null && (l_bais.length > 0)) {
		                l_img = ImageIO.read(new ByteArrayInputStream(l_bais));
		            }
				} catch (Exception e) {
					//return null...
				}
			}
		}
		
		return l_img;
	}

	public void saveErrorImage(BufferedImage p_img, TreeMap<Integer, Vector<String>> p_error_contests) {
		//Get bytestream
		ByteArrayOutputStream l_baos = new ByteArrayOutputStream();
        try {
        	ImageIO.write(p_img, "png", l_baos);
        } catch (IOException e) {
        	return;
        }	
 		//UUEncode
 		Base64 l_enc = new Base64();
	 	c_ballotImage = l_enc.encodeToString(l_baos.toByteArray());
	 	
	 	c_errorContests = p_error_contests; 
	 	
	}
	
	public BufferedImage getImage() {
		BufferedImage l_img = null; 
		
		String l_str = c_ballotImage;
		Base64 l_dec = new Base64();
		//Decode and read in the image.
		try {
			byte[] l_bais = l_dec.decode(l_str);
            if (l_bais != null && (l_bais.length > 0)) {
                l_img = ImageIO.read(new ByteArrayInputStream(l_bais));
            }
		} catch (Exception e) {
			//return null...
		}
		
		return l_img; 
	}
	
	public String getBallotImage() { 
		return c_ballotImage; 
	}
	
	public void setBallotImage(String p_ballotImage) {
		c_ballotImage = p_ballotImage;  
	}
	
	public TreeMap<Integer, Vector<String>> getErrorContests() {
		return c_errorContests; 
	}
	
	public void setErrorContests(TreeMap<Integer, Vector<String>> p_errorContests) {
		c_errorContests = p_errorContests;
	}
		
}
