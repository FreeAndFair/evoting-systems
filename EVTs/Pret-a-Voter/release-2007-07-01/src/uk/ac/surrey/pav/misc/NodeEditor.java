package uk.ac.surrey.pav.misc;

import java.awt.Dimension;
import java.awt.Frame;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.WindowConstants;

import uk.ac.surrey.pav.administrator.treenodes.Election;
import uk.ac.surrey.pav.administrator.treenodes.NamableAndSortableTreeNode;

public class NodeEditor extends JDialog {

	private static final long serialVersionUID = 1L;

	private JPanel jContentPane = null;

	private JTextField jTextFieldName = null;

	private JButton jButtonOK = null;

	private JButton jButtonCancel = null;

	private JPanel jPanelButtonPanel = null;
	
	/**
	 * @param owner
	 */
	public NodeEditor(Frame owner, NamableAndSortableTreeNode n) {
		super(owner,"Node Editor");
		this.node=n;
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.setSize(200, 100);
		this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		this.setContentPane(getJContentPane());
	}

	/**
	 * This method initializes jContentPane
	 * 
	 * @return javax.swing.JPanel
	 */
	private JPanel getJContentPane() {
		if (jContentPane == null) {
			jContentPane = new JPanel();
			//jContentPane.setLayout(new BorderLayout());
			jContentPane.add(getJTextFieldName());
			jContentPane.add(getJPanelButtonPanel());
		}
		return jContentPane;
	}

	/**
	 * This method initializes jTextFieldName	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getJTextFieldName() {
		if (jTextFieldName == null) {
			jTextFieldName = new JTextField();
			jTextFieldName.setColumns(15);
			jTextFieldName.setText(this.node.getName());
		}
		return jTextFieldName;
	}

	/**
	 * This method initializes jButtonOK	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonOK() {
		if (jButtonOK == null) {
			jButtonOK = new JButton();
			jButtonOK.setText("OK");
			jButtonOK.setMnemonic(KeyEvent.VK_O);
			jButtonOK.addActionListener(new ButtonOKHandler(this));
			
		}
		return jButtonOK;
	}

	/**
	 * This method initializes jButtonCancel	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCancel() {
		if (jButtonCancel == null) {
			jButtonCancel = new JButton();
			jButtonCancel.setText("Cancel");
			jButtonCancel.setMnemonic(KeyEvent.VK_C);
			jButtonCancel.addActionListener(new ButtonCancelHandler(this));
			
		}
		return jButtonCancel;
	}

	/**
	 * This method initializes jPanelButtonPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getJPanelButtonPanel() {
		if (jPanelButtonPanel == null) {
			jPanelButtonPanel = new JPanel();
			//jPanelButtonPanel.setLayout();
			jPanelButtonPanel.setPreferredSize(new Dimension(300, 50));
			jPanelButtonPanel.add(getJButtonOK());
			jPanelButtonPanel.add(getJButtonCancel());
		}
		return jPanelButtonPanel;
	}
	
	public static void main(String[] args){
		NodeEditor editor = new NodeEditor(null,new Election("test",null));
		//editor.pack();
		editor.setVisible(true);
	}
	
	class ButtonOKHandler implements ActionListener {
		NodeEditor ne = null;
		public ButtonOKHandler(NodeEditor ne) {this.ne=ne;}

		public void actionPerformed(ActionEvent e) {
			node.setName(ne.getJTextFieldName().getText());
		}
	}
	class ButtonCancelHandler implements ActionListener {
		NodeEditor ne = null;
		public ButtonCancelHandler(NodeEditor ne) {this.ne=ne;}

		public void actionPerformed(ActionEvent e) {
			ne.dispose();
		}
	}
}
