package uk.ac.surrey.pav.administrator;

import java.awt.Dimension;
import java.awt.Frame;
import java.awt.Rectangle;
import java.awt.Toolkit;

import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JProgressBar;
import javax.swing.WindowConstants;

import uk.ac.surrey.pav.administrator.treenodes.Root;

/**
 * A dialog box for the ballot form creation process
 * 
 * @author David Lundin
 *
 */
public class BallotFormCreationDialog extends JDialog {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;

	private JProgressBar jProgressBarBallotForms = null;
	
	private BallotFormCreator creator;

	/**
	 * @param owner
	 */
	public BallotFormCreationDialog(Frame owner, Root rootNode) {
		super(owner);
		initialize();
		
		//Create the creator
		this.creator = new BallotFormCreator(this, rootNode, this.getJProgressBarBallotForms());
		(new Thread(this.creator)).start();
		
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(490, 125);
		this.setTitle("Creating ballot forms");
		this.setModal(true);
		this.setResizable(false);
		this.setDefaultCloseOperation(WindowConstants.DO_NOTHING_ON_CLOSE);
		this.setVisible(false);
		this.setContentPane(getJContentPane());

		//Center dialog on screen
		Dimension dim = Toolkit.getDefaultToolkit().getScreenSize();
		int x = (dim.width - this.getWidth()) / 2;
		int y = (dim.height - this.getHeight()) / 2;
		this.setLocation(x, y);
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
			jContentPane.add(getJProgressBarBallotForms(), null);
		}
		return jContentPane;
	}

	/**
	 * This method initializes jProgressBarBallotForms	
	 * 	
	 * @return javax.swing.JProgressBar	
	 */
	private JProgressBar getJProgressBarBallotForms() {
		if (jProgressBarBallotForms == null) {
			jProgressBarBallotForms = new JProgressBar();
			jProgressBarBallotForms.setBounds(new Rectangle(30, 30, 421, 31));
			jProgressBarBallotForms.setStringPainted(true);
		}
		return jProgressBarBallotForms;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
