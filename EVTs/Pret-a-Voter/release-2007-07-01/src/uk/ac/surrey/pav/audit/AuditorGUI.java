package uk.ac.surrey.pav.audit;

import java.awt.Rectangle;
import java.io.IOException;
import java.util.Properties;

import javax.swing.JFrame;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.JScrollPane;
import javax.swing.JTable;
import javax.swing.SwingUtilities;
import java.awt.Dimension;

/**
 * A graphical user interface for the database auditing software
 * 
 * @author David Lundin
 *
 */
public class AuditorGUI extends JFrame {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;

	private JProgressBar jProgressBarTotalProgress = null;

	private JScrollPane jScrollPaneAudit = null;

	private JTable jTableAudit = null;

	private JMenuBar jJMenuBar = null;

	private JMenu jMenuFile = null;

	private JMenuItem jMenuItemFileExit = null;

	private JMenu jMenuAudit = null;

	private JMenuItem jMenuItemAuditAll = null;

	private JMenuItem jMenuItemFileSettings = null;
	
	/**
	 * A table model that displays what has happened
	 */
	private AuditTableModel auditTableModel = new AuditTableModel();
	
	/**
	 * Settings
	 */
	private AuditorSettings settings = new AuditorSettings();  //  @jve:decl-index=0:

	private JProgressBar jProgressBarPartProgress = null;

	/**
	 * This method initializes jProgressBarTotalProgress	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBarTotalProgress() {
		if (jProgressBarTotalProgress == null) {
			jProgressBarTotalProgress = new JProgressBar();
			jProgressBarTotalProgress.setBounds(new Rectangle(30, 30, 421, 31));
			jProgressBarTotalProgress.setStringPainted(true);
			jProgressBarTotalProgress.setString("Total progress (0%)");
		}
		return jProgressBarTotalProgress;
	}

	/**
	 * This method initializes jScrollPaneAudit	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneAudit() {
		if (jScrollPaneAudit == null) {
			jScrollPaneAudit = new JScrollPane();
			jScrollPaneAudit.setBounds(new Rectangle(98, 147, 416, 100));
			jScrollPaneAudit.setViewportView(getJTableAudit());
		}
		return jScrollPaneAudit;
	}

	/**
	 * This method initializes jTableAudit	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableAudit() {
		if (jTableAudit == null) {
			jTableAudit = new JTable(auditTableModel);
		}
		return jTableAudit;
	}

	/**
	 * This method initializes jJMenuBar	
	 * 	
	 * @return javax.swing.JMenuBar	
	 */
	private JMenuBar getJJMenuBar() {
		if (jJMenuBar == null) {
			jJMenuBar = new JMenuBar();
			jJMenuBar.add(getJMenuFile());
			jJMenuBar.add(getJMenuAudit());
		}
		return jJMenuBar;
	}

	/**
	 * This method initializes jMenuFile	
	 * 	
	 * @return javax.swing.JMenu	
	 */
	private JMenu getJMenuFile() {
		if (jMenuFile == null) {
			jMenuFile = new JMenu();
			jMenuFile.setText("File");
			jMenuFile.add(getJMenuItemFileSettings());
			jMenuFile.add(getJMenuItemFileExit());
		}
		return jMenuFile;
	}

	/**
	 * This method initializes jMenuItemFileExit	
	 * 	
	 * @return javax.swing.JMenuItem	
	 */
	private JMenuItem getJMenuItemFileExit() {
		if (jMenuItemFileExit == null) {
			jMenuItemFileExit = new JMenuItem();
			jMenuItemFileExit.setText("Exit");
			jMenuItemFileExit.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					System.exit(0);
					
				}
			});
		}
		return jMenuItemFileExit;
	}

	/**
	 * This method initializes jMenuAudit	
	 * 	
	 * @return javax.swing.JMenu	
	 */
	private JMenu getJMenuAudit() {
		if (jMenuAudit == null) {
			jMenuAudit = new JMenu();
			jMenuAudit.setText("Audit");
			jMenuAudit.add(getJMenuItemAuditAll());
		}
		return jMenuAudit;
	}

	/**
	 * This method initializes jMenuItemAuditAll	
	 * 	
	 * @return javax.swing.JMenuItem	
	 */
	private JMenuItem getJMenuItemAuditAll() {
		if (jMenuItemAuditAll == null) {
			jMenuItemAuditAll = new JMenuItem();
			jMenuItemAuditAll.setText("All");
			jMenuItemAuditAll.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					auditAll();
					
				}
			});
		}
		return jMenuItemAuditAll;
	}

	/**
	 * This method initializes jMenuItemFileSettings	
	 * 	
	 * @return javax.swing.JMenuItem	
	 */
	private JMenuItem getJMenuItemFileSettings() {
		if (jMenuItemFileSettings == null) {
			jMenuItemFileSettings = new JMenuItem();
			jMenuItemFileSettings.setText("Database settings");
			jMenuItemFileSettings.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					showSettingsDialog();
					
				}
			});
		}
		return jMenuItemFileSettings;
	}

	/**
	 * This method initializes jProgressBarPartProgress	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBarPartProgress() {
		if (jProgressBarPartProgress == null) {
			jProgressBarPartProgress = new JProgressBar();
			jProgressBarPartProgress.setBounds(new Rectangle(45, 90, 436, 31));
			jProgressBarPartProgress.setString("Current action progress (0%)");
			jProgressBarPartProgress.setStringPainted(true);
		}
		return jProgressBarPartProgress;
	}

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				AuditorGUI thisClass = new AuditorGUI();
				thisClass.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
				thisClass.setVisible(true);
			}
		});
	}

	/**
	 * This is the default constructor
	 */
	public AuditorGUI() {
		super();
		
		try {
			
			//Load settings
			Properties props = new Properties();
	        props.load(Class.class.getResourceAsStream("/uk/ac/surrey/pav/audit/Auditor.prop"));
	        
	        this.settings.setDatabaseConnectionString(props.getProperty("dbconnstring"));
	        this.settings.setDatabaseUserName(props.getProperty("dbusername"));
	        this.settings.setDatabasePassword(props.getProperty("dbpassword"));
			
		} catch (IOException e) {
			e.printStackTrace();
		}

		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(657, 484);
		this.setJMenuBar(getJJMenuBar());
		this.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		this.setContentPane(getJContentPane());
		this.setTitle("Prêt à Voter database auditor");
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(getJProgressBarTotalProgress(), null);
			jContentPane.add(getJScrollPaneAudit(), null);
			jContentPane.add(getJProgressBarPartProgress(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentAdapter() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					//The margin
					int margin = 15;
					
					//Set sizes of everything
					getJProgressBarTotalProgress().setSize(jContentPane.getWidth() - (2 * margin), getJProgressBarTotalProgress().getHeight());
					getJProgressBarTotalProgress().setLocation(margin, margin);
					getJProgressBarPartProgress().setSize(jContentPane.getWidth() - (2 * margin), getJProgressBarTotalProgress().getHeight());
					getJProgressBarPartProgress().setLocation(margin, getJProgressBarTotalProgress().getLocation().y + getJProgressBarTotalProgress().getHeight() + margin);
					getJScrollPaneAudit().setSize(jContentPane.getWidth() - (2 * margin), jContentPane.getHeight() - getJProgressBarTotalProgress().getHeight() - getJProgressBarPartProgress().getHeight() - (4 * margin));
					getJScrollPaneAudit().setLocation(margin, getJProgressBarTotalProgress().getLocation().y + getJProgressBarTotalProgress().getHeight() + margin + getJProgressBarPartProgress().getHeight() + margin);
					
				}
			});
		}
		return jContentPane;
	}
	
	/**
	 * Shows the settings dialog
	 *
	 */
	private void showSettingsDialog() {
		
		(new AuditorSettingsDialog(this, settings)).setVisible(true);
		
	}
	
	/**
	 * Audit everything
	 *
	 */
	private void auditAll() {
		Auditor auditor = new Auditor(this.settings, this.auditTableModel, getJProgressBarTotalProgress(), getJProgressBarPartProgress());
		//(new ProgressBarUpdatorThread(auditor, getJProgressBarTotalProgress(), getJProgressBarPartProgress())).start();
		(new AuditorThread(auditor)).start();
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
