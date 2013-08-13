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

package actionparser;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.font.FontRenderContext;
import java.awt.geom.AffineTransform;
import java.awt.geom.Rectangle2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import javax.imageio.ImageIO;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.filechooser.FileFilter;

import tap.BallotImageHelper;

/**
 * View for BallotResultParser.
 * 
 * @author Montrose
 */
public class ResultView extends JFrame {
	private static final long serialVersionUID = 1L;
	private static final String NONE_STRING = "(NO CHOICE)";

	/**
	 * Constructs a new ResultView
	 * 
	 * @param results - List of RaceResults to display
	 * @param ballotFile - ballot file to pull images out of
	 */
	public ResultView(List<RaceResult> results, File ballotFile){
		super("Results");
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		
		Map<String, Image> titleMap = BallotImageHelper.loadBallotTitles(ballotFile);
		Map<String, Image> raceMap = loadBallotRaces(ballotFile.getAbsolutePath(), null);
		
		raceMap.put("(none)", generateNoneImage());
		
		final JPanel center = new JPanel();
		
		BoxLayout layout = new BoxLayout(center, BoxLayout.Y_AXIS);
		center.setLayout(layout);
		
		for(RaceResult res : results){
			Image title = null;
			
			if(titleMap != null && res.get_res().size() > 0)
				title = titleMap.get(res.get_res().get(0));
			
			if(title == null && titleMap != null)
				title = titleMap.get(res.get_UID());
			
			if(title != null){
				JPanel titlePanel = new JPanel();
				BoxLayout t = new BoxLayout(titlePanel, BoxLayout.X_AXIS);
				titlePanel.setLayout(t);
				titlePanel.add(new JLabel(new ImageIcon(title)));
				titlePanel.add(Box.createHorizontalGlue());
				
				center.add(titlePanel);
			}else{
				System.out.println("Omitting title card...");
			}
			
			for(String resStr : res.get_res()){
				JPanel indented = new JPanel();
				BoxLayout l = new BoxLayout(indented, BoxLayout.X_AXIS);
				indented.setLayout(l);

				if(title != null)
					indented.add(Box.createHorizontalStrut(30));
				
				System.out.println(resStr +" for "+res.get_UID());
				
				if(raceMap.get(resStr) != null){
					indented.add(new JLabel(new ImageIcon(raceMap.get(resStr))));
					indented.add(Box.createHorizontalGlue());

					center.add(indented);
				}else{
					System.out.println("Omitting race card for: "+resStr);
				}
			}
		}//for
		
		//center.add(Box.createVerticalGlue());
		
		setLayout(new BorderLayout());
		
		add(new JScrollPane(center), BorderLayout.CENTER);
		
		setSize(1024, 768);
		
		JButton saveScreen = new JButton("Save Screen Capture");
		saveScreen.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent e) {
				scrapScreen(center);
			}
		});
		
		add(saveScreen, BorderLayout.SOUTH);
	}
	
	protected void scrapScreen(JComponent comp){
		BufferedImage img = new BufferedImage(comp.getWidth(), comp.getHeight(), BufferedImage.TYPE_INT_ARGB);
		
		comp.paintAll(img.getGraphics());
		
		JFileChooser chooser = new JFileChooser();
		chooser.setFileFilter(new FileFilter(){
			@Override
			public boolean accept(File f) {
				return f.isDirectory() || f.getName().toLowerCase().endsWith(".png");
			}

			@Override
			public String getDescription() {
				return ".PNG Image File";
			}
			
		});
		if(chooser.showSaveDialog(this) != JFileChooser.APPROVE_OPTION){
			return;
		}
		
		File file = chooser.getSelectedFile();
		
		if(!file.getName().endsWith(".png")){
			file = new File(file.getAbsolutePath()+".png");
		}
		
		try{
			ImageIO.write(img, "PNG", file);
		}catch(Exception e){
			throw new RuntimeException(e);
		}
	}
	
	protected Image generateNoneImage(){
		BufferedImage img = new BufferedImage(300,40, BufferedImage.TYPE_INT_ARGB);
		Graphics g = img.getGraphics();
		g.setFont(g.getFont().deriveFont(16));
		g.setColor(Color.black);
		
		Rectangle2D rect = g.getFont().getStringBounds(NONE_STRING, new FontRenderContext(new AffineTransform(), true, true));
		
		g.drawString(NONE_STRING, 0, (int)(40/2 + rect.getHeight()/2));
		
		return img;
	}
	
	/**
	 * Taking in a ballot location, tries to load all relavent images into a map of race-ids to Images.
	 * 
	 * @param ballot - The ballot file to read
	 * @param languages - The list of languages in the ballot file
	 * @return a map of race-ids to images, or null if an error was encountered.
	 */
	private static Map<String, Image> loadBallotRaces(String ballot, List<String> languages) {
		try {
			Map<String, Image> racesToImageMap = new HashMap<String, Image>();
			
			ZipFile file = new ZipFile(ballot);
			
			Enumeration<? extends ZipEntry> entries = file.entries();
			
			while(entries.hasMoreElements()){
				ZipEntry entry = entries.nextElement();
				
				if(isRaceImage(entry.getName(), languages)){
					racesToImageMap.put(getRace(entry.getName()), ImageIO.read(file.getInputStream(entry)));
				}//if
			}//while
			
			return racesToImageMap;
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}
	
	/**
	 * @param entryName - the Zip entry to consider
	 * @return true if entryName is in the form "media_B*_selected_*.png", ie if it is a "race image"
	 */
	private static boolean isRaceImage(String entryName, List<String> langs){
		if(!entryName.startsWith("media/B"))
			return false;
		
		if(!entryName.endsWith(".png"))
			return false;
		
		if(entryName.indexOf("_selected_") == -1 && entryName.indexOf("_focusedSelected_") == -1 && entryName.indexOf("_focused_") == -1)
			return false;
		
		if(langs != null)
			if(entryName.indexOf(langs.get(0)) == -1) //grab the first language for now
				return false;
		
		return true;
	}//isRaceImage
	
	/**
	 * Extracts a race-id from a zip entry of a race image.
	 * 
	 * @param name - the entry of the race image.
	 * @return A string in the form B*, that is a valid race id
	 */
	private static String getRace(String name) {
		int start = name.indexOf('B');
		int end = name.indexOf('_');
		
		return name.substring(start, end);
	}
}