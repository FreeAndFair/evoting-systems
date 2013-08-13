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

package tap;

import java.awt.Image;
import java.awt.image.BufferedImage;
import java.awt.image.PixelGrabber;
import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import javax.imageio.ImageIO;

import votebox.middle.IBallotVars;
import votebox.middle.IncorrectTypeException;
import votebox.middle.ballot.Ballot;
import votebox.middle.ballot.BallotParser;
import votebox.middle.ballot.BallotParserException;
import votebox.middle.ballot.Card;
import votebox.middle.ballot.SelectableCardElement;
import votebox.middle.driver.Driver;
import votebox.middle.driver.GlobalVarsReader;

public class BallotImageHelper {
	
	/**
	 * Loads a map of "race-id" to "title label" from a ballot.
	 * 
	 * @param ballotFile - the ballot file
	 * @return a map if it exists, or null otherwise
	 */
	public static Map<String, Image> loadBallotTitles(File ballotFile){
		return loadBallotTitles(ballotFile.getAbsolutePath());
	}
	
	/**
	 * Loads the VVPAT ready files from the ballot.
	 * 
	 * @param ballotFile - the ballot file
	 * @return a map of "image-id" (L**, B**, etc.) to vvpat ready images.
	 */
	public static Map<String, Image> loadImagesForVVPAT(File ballotFile){
		return loadImagesForVVPAT(ballotFile.getAbsolutePath());
	}
	
	/**
	 * Loads the VVPAT ready files from the ballot.
	 * 
	 * @param ballotPath - the path to the ballot file
	 * @return a map of "image-id" (L**, B**, etc.) to vvpat ready images.
	 */
	public static Map<String, Image> loadImagesForVVPAT(String ballotPath){
		Map<String, Image> vvpatMap = new HashMap<String, Image>();
		try{
			ZipFile file = new ZipFile(ballotPath);
			Enumeration<? extends ZipEntry> entries = file.entries();
			
			while(entries.hasMoreElements()){
				ZipEntry entry = entries.nextElement();
				
				if(entry.getName().endsWith("/vvpat/accept.png"))
					vvpatMap.put("accept", ImageIO.read(file.getInputStream(entry)));
				
				if(entry.getName().endsWith("/vvpat/spoil.png"))
					vvpatMap.put("spoil", ImageIO.read(file.getInputStream(entry)));
				
				if(entry.getName().endsWith(".png") && entry.getName().contains("/vvpat/")){
					String id = entry.getName();
					id = id.substring(id.lastIndexOf("/vvpat/")+ 7);
					
					int sub = id.indexOf("_");
					
					if(sub == -1) continue;
					
					id = id.substring(0, sub);
					
					vvpatMap.put(id, ImageIO.read(file.getInputStream(entry)));
				}
			}
		}catch(Exception e){
			System.out.println("BallotImageHelper ERROR: "+e.getMessage());
			return null;
		}
		
		return vvpatMap;
	}
	
	/**
	 * Loads a map of "race-id" to "title label" from a ballot.
	 * 
	 * @param ballotPath - path to the ballot file
	 * @return a map if it exists, or null otherwise
	 */
	public static Map<String, Image> loadBallotTitles(String ballotPath) {
		Map<String, Image> titleMap = new HashMap<String, Image>();

		try {
			Ballot ballot = getBallot(ballotPath);

			List<Card> cards = ballot.getCards();

			for(Card card : cards){
				try{
					String label = card.getProperties().getString("TitleLabelUID");
					if(label != null){
						Image labelImg = loadLabel(label, ballotPath);
						for(SelectableCardElement element : card.getElements()){
							titleMap.put(element.getUniqueID(), labelImg);
						}//for
						
						//So a lookup on the CARD will get the title image
						titleMap.put(card.getUniqueID(), labelImg);
					}//if
				}catch(IncorrectTypeException e){
					//Fail silently, and move on
				}
			}//for
		} catch (IOException e) {
			System.err.println("BallotImageHelper ERROR: "+e.getMessage());
			return null;
		} catch (BallotParserException e) {
			System.err.println("BallotImageHelper ERROR: "+e.getMessage());
			return null;
		}

		//If we didn't get ANY title images, act like we failed.
		if(titleMap.size() == 0) return null;

		return titleMap;
	}

	/**
	 * Loads the image associated with the given label uid.
	 * 
	 * @param label - string in the form L??, as a valid uid.
	 * @param ballot - the path to the ballot file
	 * @return the corresponding image.
	 */
	private static Image loadLabel(String label, String ballot) {
		try {
			ZipFile file = new ZipFile(ballot);


			Enumeration<? extends ZipEntry> entries = file.entries();

			while(entries.hasMoreElements()){
				ZipEntry entry = entries.nextElement();
				String name = entry.getName();

				boolean isLabel = name.startsWith("media/"+label+"_1_") && name.endsWith(".png");

				if(isLabel){
					BufferedImage image = ImageIO.read(file.getInputStream(entry));

					return trimImage(image);
				}//if
			}//while
		} catch (IOException e) {
			throw new RuntimeException(e);
		}

		throw new RuntimeException("Couldn't load image associated with label <"+label+"> from <"+ballot+">");
	}

	/**
	 * Trims the given image so that there is no leading white/transparent block.
	 * 
	 * @param image - Image to trim
	 * @return trimmed image
	 */
	private static Image trimImage(BufferedImage image) {
		try{
			int[] pix = new int[image.getWidth() * image.getHeight()];
			PixelGrabber grab = new PixelGrabber(image, 0, 0, image.getWidth(), image.getHeight(), pix, 0, image.getWidth());
			if(!grab.grabPixels()) return image;

			int lastClearRow = 0;
			out:
				for(int x = 1; x < image.getWidth(); x++){
					for(int y = 0; y < image.getHeight(); y++){
						int i = y*image.getWidth() + x;
						int pixel = pix[i];

						int alpha = (pixel >> 24) & 0xff;
						int red   = (pixel >> 16) & 0xff;
						int green = (pixel >>  8) & 0xff;
						int blue  = (pixel      ) & 0xff;

						if(alpha == 0) continue;
						if(red == 255 && green == 255 && blue == 255) continue;

						break out;
					}//for
					lastClearRow = x;
				}//for

				return image.getSubimage(lastClearRow, 0, image.getWidth() - lastClearRow, image.getHeight());
		}catch(InterruptedException e){ return image; }		
	}

	/**
	 * Grabs the list of languages from the ballot if it exists
	 * 
	 * @param ballotPath - the path to the ballot
	 * @return the list of languages in string form, or null if there was a problem (ex. only 1 language)
	 */
	public static List<String> getLanguages(String ballotPath){
		try {
			Ballot ballot = getBallot(ballotPath);

			List<String> lang;
			try {
				lang = ballot.getProperties().getStringList("Languages");
			} catch (IncorrectTypeException e) {
				lang = null;
			}
			return lang;
		} catch (IOException e) {
			return null;
		} catch (BallotParserException e) {
			return null;
		}

	}

	/**
	 * Takes the ballot path and returns the ballot in Ballot form
	 * 
	 * @param ballotPath - the path to the ballot zip file
	 * @return the Ballot
	 * @throws IOException
	 * @throws BallotParserException
	 */
	private static Ballot getBallot(String ballotPath) throws IOException, BallotParserException {
		//GlobalVarsReader et. al. expect the ballot to be extracted.
		//This is a very stupid assumption (why we aren't taking InputStreams is beyond me) but
		//needs to hold for now.
		File tempBallotPath = File.createTempFile("ballot", "path");
		tempBallotPath.delete();
		tempBallotPath = new File(tempBallotPath,"data");
		tempBallotPath.mkdirs();

		Driver.unzip(ballotPath, tempBallotPath.getAbsolutePath());

		IBallotVars vars = new GlobalVarsReader(tempBallotPath.getAbsolutePath()).parse();

		BallotParser parser = new BallotParser();
		return parser.getBallot(vars);
	}
}
