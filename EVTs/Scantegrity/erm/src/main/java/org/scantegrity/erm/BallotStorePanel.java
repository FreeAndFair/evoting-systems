package org.scantegrity.erm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.event.ActionListener;
import java.io.File;
import java.io.IOException;
import java.security.NoSuchAlgorithmException;
import java.util.Collection;
import java.util.HashSet;
import java.util.TreeMap;
import java.util.Vector;
import java.util.regex.Pattern;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.border.TitledBorder;
import javax.swing.filechooser.FileNameExtensionFilter;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.TableModel;

import org.apache.commons.io.FileUtils;
import org.scantegrity.common.FindFile;
import org.scantegrity.common.RandomBallotStore;

public class BallotStorePanel extends JPanel {

	private static final long serialVersionUID = 1L;
	private JScrollPane foundScrollPane = null;
	private JScrollPane loadedScrollPane = null;
	private JPanel centerPanel = null;
	private JPanel arrowButtonPanel = null;
	private JPanel buttonPanel = null;
	private JButton loadButton = null;
	private JButton unloadButton = null;
	private JButton findButton = null;
	private JButton browseButton = null;
	private JTable foundTable = null;
	private AbstractTableModel foundModel = null;  //  @jve:decl-index=0:
	private Vector<FoundRow> foundData = new Vector<FoundRow>();  //  @jve:decl-index=0:
	private JTable loadedTable = null;
	private Vector<LoadedRow> loadedData = new Vector<LoadedRow>();
	private AbstractTableModel loadedModel = null;
	private TreeMap<Integer, RandomBallotStore> c_foundStores = new TreeMap<Integer, RandomBallotStore>();  //  @jve:decl-index=0:
	private TreeMap<Integer, RandomBallotStore> c_loadedStores = new TreeMap<Integer, RandomBallotStore>();  //  @jve:decl-index=0:
	private TreeMap<Integer, RandomBallotStore> c_copiedFiles = new TreeMap<Integer, RandomBallotStore>();
	//private HashSet<Integer> c_foundIds = new HashSet<Integer>();  //  @jve:decl-index=0:
	//private HashSet<Integer> c_loadedIds = new HashSet<Integer>();  //  @jve:decl-index=0:
	private FinderThread c_findThread = null;  //  @jve:decl-index=0:
	private WriteInResolver c_resolver = null;
	private ErrorBallotResolver c_errorResolver = null;
	private String c_path = null;
	private StatisticsPanel c_panel = null;
	
	class FoundRow
	{
		public String scannerId;
		public String filePath;
		public FoundRow(String p_scannerId, String p_filePath)
		{
			scannerId = p_scannerId;
			filePath = p_filePath;
		}
	}
	
	class LoadedRow
	{
		public String scannerId;
		public String filePath;
		public String loading;
		public LoadedRow(String p_scannerId, String p_filePath)
		{
			scannerId = p_scannerId;
			filePath = p_filePath;
			loading = "Loading...";
		}
	}

	/**
	 * This is the default constructor
	 */
	public BallotStorePanel(WriteInResolver p_resolver, ErrorBallotResolver p_errorResolver, 
			String p_path, StatisticsPanel p_panel) {
		super();
		c_panel = p_panel;
		c_resolver = p_resolver;
		c_errorResolver = p_errorResolver; 
		c_path = p_path;
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(500, 300);
		this.setLayout(new BorderLayout());
		this.add(getCenterPanel(), BorderLayout.CENTER);
		this.add(getButtonPanel(), BorderLayout.SOUTH);
		c_findThread = new FinderThread();
		c_findThread.start();
	}

	/**
	 * This method initializes centerPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private Component getCenterPanel() {
		if (centerPanel == null) {
			centerPanel = new JPanel();
			centerPanel.setLayout(new BorderLayout());
			centerPanel.add(getFoundScrollPane(), BorderLayout.WEST);
			centerPanel.add(getLoadedScrollPane(), BorderLayout.EAST);
			centerPanel.add(getArrowButtonPanel(), BorderLayout.CENTER);
		}
		return centerPanel;
	}

	/**
	 * This method initializes foundScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getFoundScrollPane() {
		if (foundScrollPane == null) {
			foundScrollPane = new JScrollPane();
			foundScrollPane.setBorder(BorderFactory.createTitledBorder(null, "Found Ballot Stores", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			foundScrollPane.setViewportView(getFoundTable());
		}
		return foundScrollPane;
	}

	/**
	 * This method initializes loadedScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getLoadedScrollPane() {
		if (loadedScrollPane == null) {
			loadedScrollPane = new JScrollPane();
			loadedScrollPane.setBorder(BorderFactory.createTitledBorder(null, "Loaded Ballot Stores", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			loadedScrollPane.setViewportView(getLoadedTable());
		}
		return loadedScrollPane;
	}

	/**
	 * This method initializes arrowButtonPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getArrowButtonPanel() {
		if (arrowButtonPanel == null) {
			arrowButtonPanel = new JPanel();
			arrowButtonPanel.setLayout(new BorderLayout());
			arrowButtonPanel.add(getLoadButton(), BorderLayout.NORTH);
			arrowButtonPanel.add(getUnloadButton(), BorderLayout.SOUTH);
		}
		return arrowButtonPanel;
	}

	/**
	 * This method initializes buttonPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getButtonPanel() {
		if (buttonPanel == null) {
			buttonPanel = new JPanel();
			buttonPanel.setLayout(new GridBagLayout());
			buttonPanel.add(getFindButton(), new GridBagConstraints());
			buttonPanel.add(getBrowseButton(), new GridBagConstraints());
		}
		return buttonPanel;
	}

	/**
	 * This method initializes loadButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getLoadButton() {
		if (loadButton == null) {
			loadButton = new JButton();
			loadButton.setText(">");
			loadButton.setPreferredSize(new Dimension(20,20));
			loadButton.addActionListener(new ActionListener(){
				public void actionPerformed(java.awt.event.ActionEvent e) {
					loadSelectedBallotStore();
				}
			});
		}
		return loadButton;
	}

	/**
	 * This method initializes unloadButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getUnloadButton() {
		if (unloadButton == null) {
			unloadButton = new JButton();
			unloadButton.setText("<");
			unloadButton.setPreferredSize(new Dimension(20,20));
			unloadButton.addActionListener(new ActionListener(){
				public void actionPerformed(java.awt.event.ActionEvent e) {
					unloadSelectedBallotStore();
				}
			});
		}
		return unloadButton;
	}

	/**
	 * This method initializes findButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getFindButton() {
		if (findButton == null) {
			findButton = new JButton();
			findButton.setText("Find Ballots");
			findButton.addActionListener(new ActionListener(){
				public void actionPerformed(java.awt.event.ActionEvent e) {
					if( c_findThread != null && c_findThread.isAlive() ){
						System.out.println("Thread still alive!");
						try {
							c_findThread.join();
						} catch (InterruptedException e1) {
							// TODO Auto-generated catch block
							e1.printStackTrace();
						}
					}
					c_findThread = new FinderThread();
					c_findThread.start();
				}
			});
		}
		return findButton;
	}

	/**
	 * This method initializes browseButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getBrowseButton() {
		if (browseButton == null) {
			browseButton = new JButton();
			browseButton.setText("Browse");
			browseButton.addActionListener(new ActionListener(){
				public void actionPerformed(java.awt.event.ActionEvent e) {
					JFileChooser l_chooser = new JFileChooser();
					FileNameExtensionFilter l_filter = new FileNameExtensionFilter("Ballot Stores", "sbr");
					l_chooser.setFileFilter(l_filter);
					if( l_chooser.showOpenDialog(getParent()) == JFileChooser.APPROVE_OPTION )
					{
						loadBallotStore(l_chooser.getSelectedFile().getAbsolutePath());
					}
				}
			});
			
		}
		return browseButton;
	}

	/**
	 * This method initializes foundTable	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getFoundTable() {
		if (foundTable == null) {
			foundTable = new JTable();
			foundModel = new AbstractTableModel(){
				/**
				 * 
				 */
				private static final long serialVersionUID = 1L;
				public String getColumnName(int col) {
			        if( col == 0 )
			        	return "Scanner ID";
			        else
			        	return "Path";
			    }
			    public int getRowCount() { return foundData.size(); }
			    public int getColumnCount() { return 2; }
			    public Object getValueAt(int row, int col) {
			        if( col == 0 )
			        {
			        	return foundData.get(row).scannerId;
			        }
			        else
			        {
			        	return foundData.get(row).filePath;
			        }
			    }
			    public boolean isCellEditable(int row, int col)
			        { return false; }
			    public void setValueAt(Object value, int row, int col) {
			    }
			};
			foundTable.setModel(foundModel);
		}
		return foundTable;
	}

	/**
	 * This method initializes loadedTable	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getLoadedTable() {
		if (loadedTable == null) {
			loadedTable = new JTable();
			loadedModel = new AbstractTableModel(){
				/**
				 * 
				 */
				private static final long serialVersionUID = 1L;
				public String getColumnName(int col) {
			        if( col == 0 )
			        	return "Scanner ID";
			        else if( col == 1 )
			        	return "Path";
			        else 
			        	return "Loaded";
			    }
			    public int getRowCount() { return loadedData.size(); }
			    public int getColumnCount() { return 3; }
			    public Object getValueAt(int row, int col) {
			        if( col == 0 )
			        {
			        	return loadedData.get(row).scannerId;
			        }
			        else if( col == 1 )
			        {
			        	return loadedData.get(row).filePath;
			        }
			        else
			        	return loadedData.get(row).loading;
			    }
			    public boolean isCellEditable(int row, int col)
			        { return false; }
			    public void setValueAt(Object value, int row, int col) {
			    }
			};
			loadedTable.setModel(loadedModel);
		}
		return loadedTable;
	}
	
	public void loadBallotStore(String p_path)
	{
		synchronized(this)
		{
			try {
				RandomBallotStore l_store = new RandomBallotStore(0, 0, 0, p_path, null, null);
				l_store.open();
				if( !c_foundStores.containsKey(l_store.getScannerId()) && !c_loadedStores.containsKey(l_store.getScannerId()) )
				{
					c_foundStores.put(l_store.getScannerId(), l_store);
					addFoundStore(Integer.toString(l_store.getScannerId()), l_store.getLocation());
				}
				else
				{
					l_store.close();
				}
			} catch (NoSuchAlgorithmException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
	}
	
	public void addFoundStore(String p_id, String p_path)
	{
		FoundRow l_newRow = new FoundRow(p_id, p_path);
		foundData.add(l_newRow);
		foundModel.fireTableDataChanged();
	}
	
	public void loadSelectedBallotStore()
	{
		int l_rowIndex = foundTable.getSelectedRow();
		RandomBallotStore l_store = c_foundStores.remove(new Integer(foundData.get(l_rowIndex).scannerId));
		foundData.remove(l_rowIndex);
		foundModel.fireTableDataChanged();
		loadStore(l_store);
		
	}
	

	public void unloadSelectedBallotStore() {
		int l_rowIndex = loadedTable.getSelectedRow();
		RandomBallotStore l_store = c_loadedStores.remove(new Integer(loadedData.get(l_rowIndex).scannerId));
		loadedData.remove(l_rowIndex);
		loadedModel.fireTableDataChanged();
		unloadStore(l_store);
	}

	public void loadStore(RandomBallotStore p_store)
	{
		if( c_loadedStores.containsKey(p_store.getScannerId()) )
		{
			if( JOptionPane.YES_OPTION != JOptionPane.showConfirmDialog(getParent(), "There is already a store loaded with that scanner ID, are you sure you would like to continue?", "Confirm Load", JOptionPane.YES_NO_OPTION) )
				return;
		}
		LoadedRow l_newRow = new LoadedRow(Integer.toString(p_store.getScannerId()), p_store.getLocation());
		loadedData.add(l_newRow);
		loadedModel.fireTableDataChanged();
		LoaderThread l_loader = new LoaderThread(l_newRow, p_store);
		l_loader.start();
	}
	
	public void unloadStore(RandomBallotStore p_store) 
	{
		FoundRow l_newRow = new FoundRow(Integer.toString(p_store.getScannerId()), p_store.getLocation());
		foundData.add(l_newRow);
		foundModel.fireTableDataChanged();
		//have to reverse everything that is done in LoaderThread
		try {
			c_panel.removeBallotCount(c_resolver.unloadBallots(p_store));
			if(c_errorResolver != null)
				c_errorResolver.unloadBallots(p_store); 
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		c_panel.setWriteInCount(c_resolver.getWriteInCount());
		c_panel.setErrorCount(c_errorResolver.getErrorBallotCount());
		c_foundStores.put(p_store.getScannerId(), p_store);
		//TODO: Add Error Ballot stuff here
	}

	class LoaderThread extends Thread
	{
		LoadedRow c_row = null;
		RandomBallotStore c_store = null;
		
		public LoaderThread(LoadedRow p_row, RandomBallotStore p_store)
		{
			super();
			c_row = p_row;
			c_store = p_store;
		}
		
		public void run()
		{
			synchronized(c_resolver)
			{
				try {
					int l_count = c_resolver.LoadBallots(c_store);
					c_panel.addBallotCount(l_count);
					c_panel.setWriteInCount(c_resolver.getWriteInCount());
					if (c_errorResolver != null)
						c_errorResolver.LoadBallots(c_store);
					c_panel.setErrorCount(c_errorResolver.getErrorBallotCount());
					c_store.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
			int x = 1;
			String l_newFile = c_path + File.separator + "Ballots-" + c_store.getScannerId() + ".sbr";
			while( new File(l_newFile).exists() )
			{
				l_newFile = c_path + File.separator + "Ballots-" + c_store.getScannerId() + "-" + x + ".sbr";
				x++;
			}
			
			try {
				FileUtils.copyFile(new File(c_store.getLocation()), new File(l_newFile));
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			c_loadedStores.put(c_store.getScannerId(), c_store);
			
			c_row.loading = "Done";
			loadedModel.fireTableDataChanged();
		}
	}
	
	class FinderThread extends Thread implements FindFile.AsyncFindListener
	{
		public void run()
		{
			findButton.setText("Searching...");
			findButton.setEnabled(false);
			
			Collection<RandomBallotStore> l_collection = c_foundStores.values(); 
			for( RandomBallotStore l_store : l_collection )
			{
				try {
					l_store.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			
			c_foundStores.clear();
			foundData.clear();
			foundModel.fireTableDataChanged();

			FindFile l_finder = new FindFile(Pattern.compile(".*\\.sbr"));
			l_finder.c_recurseDepth = 2;
			Thread l_findThread = l_finder.findAsync(this);
			
			try {
				l_findThread.join();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			findButton.setText("Find Ballots");
			findButton.setEnabled(true);
		}

		@Override
		public void report(File p_file) {
			//System.out.println("Found file: " + p_file.getPath());
			loadBallotStore(p_file.getPath());
			
		}
	}

}
