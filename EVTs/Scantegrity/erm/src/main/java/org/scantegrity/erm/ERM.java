package org.scantegrity.erm;

import java.awt.Component;
import java.beans.XMLDecoder;
import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JTabbedPane;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;
import javax.swing.filechooser.FileNameExtensionFilter;

import org.scantegrity.common.FindFile;
import org.scantegrity.scanner.ScannerConfig;
import org.scantegrity.scanner.ScannerConstants;

public class ERM extends JFrame {

	private static final long serialVersionUID = 1L;
	private JTabbedPane jTabbedPane = null;
	private WriteInPanel writeInPanel = null;
	private ErrorPanel errorPanel = null;
	private File c_scannerConfigFile = null;
	private ScannerConfig c_config = null;
	private TallyPanel tallyPanel = null;
	private LoadPanel loadPanel = null;
	private SpoiledPanel spoiledPanel = null;
	public WriteInResolver c_resolver = null;
	public WriteInResolver c_spoiledResolver = null;
	private String c_path = null;
	private ErrorBallotResolver c_errorBallotResolver = null;
	
	/**
	 * This method initializes jTabbedPane	
	 * 	
	 * @return javax.swing.JTabbedPane	
	 */
	private JTabbedPane getJTabbedPane() {
		if (jTabbedPane == null) {
			jTabbedPane = new JTabbedPane();
			jTabbedPane.addTab("Load Ballots", null, getLoadPanel(), null);
			jTabbedPane.addTab("Write-In Resolution", null, getWriteInPanel(), null);
			jTabbedPane.addTab("Voting Error Resolution", null, getErrorPanel(), null);
			jTabbedPane.addTab("Spoiled Ballots", null, getSpoiledPanel(), null);
			jTabbedPane.addTab("Tally", null, getTallyPanel(), null);
		}
		return jTabbedPane;
	}

	/** 
	 * The error panel shows the user all of the ballots 
	 * with voting errors, displaying the ballot on the 
	 * screen and allowing the user to resolve issues with 
	 * the ballot so the ballot can be properly cast.  
	 */
	private Component getErrorPanel() {
		if (errorPanel == null) {
			errorPanel = new ErrorPanel(c_errorBallotResolver);
		}
		return errorPanel;
	}

	/**
	 * This method initializes writeInPanel	
	 * 	
	 * @return scantegrity.erm.WriteInPanel	
	 */
	private WriteInPanel getWriteInPanel() {
		if (writeInPanel == null) {
			writeInPanel = new WriteInPanel(c_resolver);
		}
		return writeInPanel;
	}

	/**
	 * This method initializes tallyPanel	
	 * 	
	 * @return org.scantegrity.erm.TallyPanel	
	 */
	private TallyPanel getTallyPanel() {
		if (tallyPanel == null) {
			tallyPanel = new TallyPanel(c_resolver, c_spoiledResolver, c_errorBallotResolver, c_path);
		}
		return tallyPanel;
	}

	/**
	 * This method initializes loadPanel	
	 * 	
	 * @return org.scantegrity.erm.LoadPanel	
	 */
	private LoadPanel getLoadPanel() {
		if (loadPanel == null) {
			loadPanel = new LoadPanel(c_resolver, c_errorBallotResolver, c_path);
		}
		return loadPanel;
	}

	/**
	 * This method initializes spoiledPanel	
	 * 	
	 * @return org.scantegrity.erm.SpoiledPanel	
	 */
	private SpoiledPanel getSpoiledPanel() {
		if (spoiledPanel == null) {
			spoiledPanel = new SpoiledPanel(c_spoiledResolver, c_path + File.separator + "Audit");
		}
		return spoiledPanel;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				try {
					UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
				} catch (ClassNotFoundException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (InstantiationException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (IllegalAccessException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				} catch (UnsupportedLookAndFeelException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				ERM thisClass = new ERM();
				thisClass.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
				thisClass.setVisible(true);
			}
		});
	}

	/**
	 * This is the default constructor
	 */
	public ERM() {
		super();
		FindFile l_finder = new FindFile(ScannerConstants.DEFAULT_CONFIG_NAME);
		l_finder.c_recurseDepth = 1;
		c_scannerConfigFile = l_finder.find();
		if( c_scannerConfigFile == null )
		{
			JOptionPane.showMessageDialog(getParent(), "Could not locate configuration file, please provide a path to " + ScannerConstants.DEFAULT_CONFIG_NAME);
			JFileChooser l_fileChooser = new JFileChooser();
			FileNameExtensionFilter l_filter = new FileNameExtensionFilter("Xml Configuration File", "xml");
			l_fileChooser.setFileFilter(l_filter);
			int l_ret = JFileChooser.CANCEL_OPTION;
			while( l_ret != JFileChooser.APPROVE_OPTION )
			{
				l_ret = l_fileChooser.showOpenDialog(getParent());
			}
			c_scannerConfigFile = l_fileChooser.getSelectedFile();
		}
		
		try
		{
			XMLDecoder l_dec = new XMLDecoder(new BufferedInputStream(new FileInputStream(c_scannerConfigFile)));
			c_config = (ScannerConfig)l_dec.readObject();
			l_dec.close();	
			c_resolver = new WriteInResolver(c_config, this);
			c_errorBallotResolver = new ErrorBallotResolver(c_config, this, c_resolver); 
		}
		catch(FileNotFoundException e_fnf)
		{
			JOptionPane.showMessageDialog(getParent(), "Error loading scanner config file!");
			System.exit(-1);
		}
		
		JOptionPane.showMessageDialog(getParent(), "Please choose a directory to store results files.");
		JFileChooser l_chooser = new JFileChooser();
		l_chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
		
		boolean l_canWrite = false;
		while( !l_canWrite )
		{
			while( l_chooser.showSaveDialog(getParent()) != JFileChooser.APPROVE_OPTION )
			{}
			
			File l_selected = l_chooser.getSelectedFile();
			System.err.println("Path: " + l_selected.getPath());
			l_canWrite = l_selected.canWrite();
			if( !l_canWrite )
			{
				JOptionPane.showMessageDialog(getParent(),"Cannot write to chosen directory" );
			}
		}
		c_path = l_chooser.getSelectedFile().getPath();
		
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		c_resolver = new WriteInResolver(c_config, this);
		c_spoiledResolver = new WriteInResolver(c_config, false, this);
		c_errorBallotResolver  = new ErrorBallotResolver(c_config, true, this, c_resolver);
		this.setSize(1024, 768);
		this.setContentPane(getJTabbedPane());
		this.setTitle("Election Resolution Manager");
	}

	public void disableTabs() {
		jTabbedPane.setEnabledAt(jTabbedPane.indexOfTab("Load Ballots"), false);
		jTabbedPane.setEnabledAt(jTabbedPane.indexOfTab("Write-In Resolution"), false);
		
	}

}
