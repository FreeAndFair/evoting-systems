package uk.ac.surrey.pav.bulletinboard.tally;

import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTable;

import uk.ac.surrey.pav.bulletinboard.tablemodels.TallyTableModel;

/**
 * GUI that displays information about a tally to the user
 * 
 * @author David Lundin
 *
 */
public class TallyDialog extends JDialog {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JPanel jContentPane = null;
	private JScrollPane jScrollPaneRounds = null;
	private JTable jTableRounds = null;
	
	/**
	 * The tally set out here
	 */
	private Tally tally;

	/**
	 * This is the default constructor
	 */
	public TallyDialog(Tally tally) {
		super();

		//Store reference to tally
		this.tally = tally;

		//Initialize
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(668, 275);
		this.setContentPane(getJContentPane());
		this.setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
		this.setTitle("Tally");
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
			jContentPane.add(getJScrollPaneRounds(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					//Set the size of the table
					int margin = 15;
					int tableWidth = jContentPane.getWidth() - 2 * margin;
					int tableHeight = jContentPane.getHeight() - 2 * margin;
					getJScrollPaneRounds().setSize(tableWidth, tableHeight);
					getJScrollPaneRounds().setLocation(margin, margin);
					
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
	 * This method initializes jScrollPaneRounds	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPaneRounds() {
		if (jScrollPaneRounds == null) {
			jScrollPaneRounds = new JScrollPane();
			jScrollPaneRounds.setBounds(new java.awt.Rectangle(15,15,631,211));
			jScrollPaneRounds.setViewportView(getJTableRounds());
		}
		return jScrollPaneRounds;
	}

	/**
	 * This method initializes jTableRounds	
	 * 	
	 * @return javax.swing.JTable	
	 */
	private JTable getJTableRounds() {
		if (jTableRounds == null) {
			jTableRounds = new JTable(new TallyTableModel(this.tally));
		}
		return jTableRounds;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
