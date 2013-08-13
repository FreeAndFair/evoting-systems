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

package supervisor.view;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Image;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import javax.imageio.ImageIO;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.JTree;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.DefaultTableModel;
import javax.swing.table.TableColumn;
import javax.swing.table.TableModel;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeCellRenderer;
import javax.swing.tree.TreeModel;

import tap.BallotImageHelper;
import votebox.AuditoriumParams;

/**
 * A dialog that goes along with {@link supervisor.model.tallier.Tallier}.  It is shown
 * whenever the supervisor closes the polls, and the report from the Tallier is
 * displayed in the dialog.
 * @author cshaw
 */
@SuppressWarnings("serial")
public class TallyDialog extends JDialog {

    /**
     * Constructs a new TallyDialog
     * @param parent the parent
     * @param results the results from the Tallier
     * @param ballot path to ballot file to use for image extraction
     */
    public TallyDialog(JPanel parent, Map<String, BigInteger> results, String ballot) {
        super((JFrame)null, "Election Results", true);
        setLocationRelativeTo(parent);
        setLayout(new GridBagLayout());
        setAlwaysOnTop(true);
        GridBagConstraints c = new GridBagConstraints();
        
        JLabel title = new MyJLabel("Election Results:");
        c.gridx = 0;
        c.gridy = 0;
        c.anchor = GridBagConstraints.LINE_START;
        c.insets = new Insets(10, 10, 0, 10);
        add(title, c);
        
        JComponent resultsField = null;
        List<String> languages = BallotImageHelper.getLanguages(ballot);
        Map<String, Image> candidateImgMap = loadBallotRaces(ballot, languages);
        Map<String, Image> titleImgMap = BallotImageHelper.loadBallotTitles(ballot);
        
        AuditoriumParams params = new AuditoriumParams("supervisor.conf");
        
        if(candidateImgMap == null || params.getUseSimpleTallyView())
        	resultsField = createBasicTable(results);
        else{
        	if(titleImgMap == null || params.getUseTableTallyView())
        		resultsField = createFancyTable(results, candidateImgMap);
        	else
        		resultsField = createFancyTreeTable(results, candidateImgMap, titleImgMap);
        }//if
        
        resultsField.setFont(new Font("Monospace", Font.PLAIN, 12));
        c.gridy = 1;
        c.weightx = 1;
        c.weighty = 1;
        c.fill = GridBagConstraints.BOTH;
        add(new JScrollPane(resultsField), c);
        
        JButton okButton = new MyJButton("OK");
        okButton.setFont(okButton.getFont().deriveFont(Font.BOLD));
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
            }
        });
        c.gridy = 2;
        c.weightx = 0;
        c.weighty = 0;
        c.anchor = GridBagConstraints.CENTER;
        c.fill = GridBagConstraints.NONE;
        c.insets = new Insets(10, 10, 10, 10);
        add(okButton, c);
        
        setSize((int)Math.max(400, getPreferredSize().getWidth()), 400);
        
        System.out.println("Results: "+results);
    }

	/**
     * Creates a fancy JTree with an invisible root node, where each child of root
     * is an image of the title for that race and each child of the title is a JTree with no header
     * of votes and candidate image columns.
     * 
     * @param results - map of each race id to a total total
     * @param candidateImgMap - map of each race id to a candidate image name
     * @param titleImgMap - map of each race id to a title label
     * @return a JTree displaying all this data as described above
     */
	private JTree createFancyTreeTable(Map<String, BigInteger> results, Map<String, Image> candidateImgMap, Map<String, Image> titleImgMap) {
		final Map<Map<String, BigInteger>, JTable> modelToView = new HashMap<Map<String, BigInteger>, JTable>();
		
		//invisible root node of tree
		DefaultMutableTreeNode root = new DefaultMutableTreeNode("root", true);
		
		Map<Image, List<String>> titleToRaces = new HashMap<Image, List<String>>();
		
		for(Image title : titleImgMap.values()){
			List<String> raceIds = new ArrayList<String>();
			for(String raceId : titleImgMap.keySet()){
				if(titleImgMap.get(raceId) == title)
					raceIds.add(raceId);
			}//for
			
			titleToRaces.put(title, raceIds);
		}//for
		
		//Building the tree model
		for(Image titleImg : titleToRaces.keySet()){
			DefaultMutableTreeNode title = new DefaultMutableTreeNode(titleImg, true);
			Map<String, BigInteger> subResults = new HashMap<String, BigInteger>();
			for(String raceId : titleToRaces.get(titleImg))
				subResults.put(raceId, results.get(raceId));

			DefaultMutableTreeNode res = new DefaultMutableTreeNode(subResults, false);
			
			root.add(title);
			title.add(res);
			
			modelToView.put(subResults, createFancyTable(subResults, candidateImgMap));
		}//for
		
		TreeModel model = new DefaultTreeModel(root);
		
		JTree tree = new JTree(model);
		tree.setEditable(false);
		tree.setRootVisible(false);
		tree.setCellRenderer(new TreeCellRenderer(){
			public Component getTreeCellRendererComponent(JTree tree,
                    Object value,
                    boolean sel,
                    boolean expanded,
                    boolean leaf,
                    int row,
                    boolean hasFocus){
				
				if(!(value instanceof DefaultMutableTreeNode))
					throw new RuntimeException("Expected DefaultMutableTreeNode, found "+value);
				
				DefaultMutableTreeNode node = (DefaultMutableTreeNode)value;
				
				value = node.getUserObject();
				
				if(value != null && value instanceof Map){
					JPanel panel = new JPanel();
					JTable table = modelToView.get(value);
					table.setMinimumSize(table.getPreferredSize());
					
					panel.add(table);
					
					return panel;
				}//if
				
				if(value != null && value instanceof Image){
					Image img = (Image)value;
					
					JLabel label = new JLabel(new ImageIcon(img));
					
					label.setMinimumSize(new Dimension(img.getWidth(null), img.getHeight(null)));
					
					return label;
				}//if
				
				return new JLabel(""+value);
			}//getTreeCellRendererComponent
		});
		
		for(int i = 0; i < tree.getRowCount(); i++)
			tree.expandRow(i);
		
		return tree;
	}//createFancyTreeTable

	/**
     * Creates a table with the columns "votes" & "candidates".
     * Votes holds the number of votes a candidate received.
     * Candidates holds an image representing the candidate that was extracted from the raceImgMap.
     * 
     * @param results - A map of race-ids to vote totals
     * @param raceImgMap - A map of race-ids to images
     * @return A fancy new JTable.
     */
	private JTable createFancyTable(final Map<String, BigInteger> results, final Map<String, Image> raceImgMap) {
		JTable fancyTable = new JTable();
		
		fancyTable.setModel(new DefaultTableModel(){
			Map.Entry[] entries = null;
			
			{
				entries = results.entrySet().toArray(new Map.Entry[0]);
				if(entries.length > 1){
					Arrays.sort(entries, new Comparator<Map.Entry>(){

						public int compare(Map.Entry arg0, Map.Entry arg1) {
							if(arg0.getValue() == null && arg1.getValue() == null)
								return 0;
							
							if(arg0.getValue() == null)
								return -1;
							
							if(arg1.getValue() == null)
								return 1;
							
							return ((BigInteger)arg1.getValue()).compareTo((BigInteger)arg0.getValue());
						}

					});
				}//if
			}
			
			public int getColumnCount(){ return 3; }
			public int getRowCount(){ return results.keySet().size(); }
			
			@Override
			public Object getValueAt(int row, int col){
				Map.Entry entry = entries[row];
				
				switch(col){
					case 0: return entry.getValue();
					case 1: return raceImgMap.get(entry.getKey());
					case 2: return entry.getKey();
					default: throw new RuntimeException(col + " >= 3 column value requested.");
				}
			}//getValueAt
			
			@Override
			public boolean isCellEditable(int row, int col){
				return false;
			}
		});
		
		TableColumn column = fancyTable.getColumnModel().getColumn(1);
		
		column.setCellRenderer(new DefaultTableCellRenderer(){
			@Override
			public void setValue(Object value){
				if(value instanceof Image){
					setIcon(new ImageIcon((Image)value));
					return;
				}//if
				
				super.setValue(value);
			}//setValue
		});
		
		fancyTable.setRowHeight(getTallestImage(raceImgMap));
		column.setWidth(getWidestImage(raceImgMap));
		column.setMinWidth(getWidestImage(raceImgMap));
		
		column.setHeaderValue("Candidate");
		fancyTable.getColumnModel().getColumn(0).setHeaderValue("Votes");
		fancyTable.getColumnModel().getColumn(0).setWidth(30);
		fancyTable.getColumnModel().getColumn(2).setHeaderValue("Race ID");
		fancyTable.getColumnModel().getColumn(2).setWidth(40);
		
		return fancyTable;
	}

	/**
	 * @param images - a Map of images
	 * @return the width of the widest image in images.
	 */
	private int getWidestImage(Map<String, Image> images){
		int widest = -1;
		
		for(Image img : images.values()){
			if(img.getWidth(null) > widest)
				widest = img.getWidth(null);
		}//for
		
		return widest;
	}//getTallestImage
	
	/**
	 * @param images - a Map of images
	 * @return the height of the tallest image in images.
	 */
	private int getTallestImage(Map<String, Image> images){
		int tallest = -1;
		
		for(Image img : images.values()){
			if(img.getHeight(null) > tallest)
				tallest = img.getHeight(null);
		}//for
		
		return tallest;
	}//getTallestImage
	
	/**
	 * Taking in a ballot location, tries to load all relevant images into a map of race-ids to Images.
	 * 
	 * @param ballot - The ballot file to read
	 * @param languages - The list of languages on the ballot
	 * @return a map of race-ids to images, or null if an error was encountered.
	 */
	private Map<String, Image> loadBallotRaces(String ballot, List<String> languages) {
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
	 * @param lang - the list of languages to pull the results from
	 * @return true if entryName is in the form "media_B*_selected_*.png", ie if it is a "race image"
	 */
	private boolean isRaceImage(String entryName, List<String> langs){
		if(!entryName.startsWith("media/B"))
			return false;
		
		if(!entryName.endsWith(".png"))
			return false;
		
		if(entryName.indexOf("_selected_") == -1)
			return false;
		if (langs != null)
			if(entryName.indexOf(langs.get(0)) == -1) //grab the first listed language for now
				return false;

		return true;
	}//isRaceImage
	
	/**
	 * Extracts a race-id from a zip entry of a race image.
	 * 
	 * @param name - the entry of the race image.
	 * @return A string in the form B*, that is a valid race id
	 */
	private String getRace(String name) {
		int start = name.indexOf('B');
		int end = name.indexOf('_');
		
		return name.substring(start, end);
	}

	/**
	 * Creates a basic table for displaying vote totals.
	 * Takes for form "race id" "votes"
	 * 
	 * @param results - A map of race ids to vote totals.
	 * @return A basic JTable to display
	 */
	private JTable createBasicTable(final Map<String, BigInteger> results) {
		TableModel model = new DefaultTableModel(){
			public int getColumnCount(){ return 2; }
			public int getRowCount(){ return results.keySet().size(); }
			public String getColumnName(int column){
				switch(column){
					case 0: return "Candidate";
					case 1: return "Votes";
					default: throw new RuntimeException(column +" >= 2 column name requested.");
				}
			}//getColumnName
			
			public Object getValueAt(int row, int col){
				Map.Entry entry = results.entrySet().toArray(new Map.Entry[0])[row];
				
				switch(col){
					case 0: return entry.getKey();
					case 1: return entry.getValue();
					default: throw new RuntimeException(col + " >= 2 column value requested.");
				}
			}//getValueAt
		};
		
		return new JTable(model);
	}
}
