package uk.ac.surrey.pav.bulletinboard;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JLabel;
import javax.swing.JPanel;

/**
 * Displays status information about the connection to and loading
 * from the database
 * 
 * @author David Lundin
 *
 */
public class DatabaseConnectorDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	
	private JPanel jContentPane = null;
	private JLabel jLabelStatus = null;
	private JButton jButtonOK = null;
	
	/**
	 * The database connector thread
	 */
	private DatabaseConnectorThread connectorThread;
	
	/**
	 * A bulletin board at caller
	 */
	private BulletinBoard bulletinBoard;

	/**
	 * This is the default constructor
	 */
	public DatabaseConnectorDialog(BulletinBoard bulletinBoard, String url, String userName, String password) {
		super();
		initialize();
		
		//Store reference to bulletin board at caller
		this.bulletinBoard = bulletinBoard;
		
		//Start the connection thread
		this.connectorThread = new DatabaseConnectorThread(this.bulletinBoard, url, userName, password, this.jLabelStatus, this.jButtonOK, this);
		this.connectorThread.start();

		//Show the window
		this.setVisible(true);
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(471, 228);
		this.setResizable(true);
		this.setModal(true);
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setTitle("Connecting to and loading from database");
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jLabelStatus = new JLabel();
			jLabelStatus.setBounds(new java.awt.Rectangle(15,15,436,121));
			jLabelStatus.setHorizontalAlignment(javax.swing.SwingConstants.CENTER);
			jLabelStatus.setHorizontalTextPosition(javax.swing.SwingConstants.CENTER);
			jLabelStatus.setText("(status)");
			jContentPane = new JPanel();
			jContentPane.setLayout(null);
			jContentPane.add(jLabelStatus, null);
			jContentPane.add(getJButtonOK(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {
					//Resize the status label
					jLabelStatus.setBounds(new java.awt.Rectangle(15, 15, jContentPane.getWidth() - 30 , jContentPane.getHeight() - 45 - jButtonOK.getHeight()));
					//Move the OK button
					jButtonOK.setLocation((jContentPane.getWidth() - jButtonOK.getWidth() - 30) / 2, jContentPane.getHeight() - jButtonOK.getHeight() - 15);
				}
				public void componentMoved(java.awt.event.ComponentEvent e) {
				}
				public void componentShown(java.awt.event.ComponentEvent e) {
				}
				public void componentHidden(java.awt.event.ComponentEvent e) {
				}
			});
		}
		return jContentPane;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setBounds(new java.awt.Rectangle(180,150,106,31));
			jButtonOK.setEnabled(false);
			jButtonOK.setText("OK");
			jButtonOK.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					setVisible(false);
				}
			});
		}
		return jButtonOK;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
