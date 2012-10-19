package org.scantegrity.engine.gui;

import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTextField;

import javax.swing.WindowConstants;

import com.sun.org.apache.xerces.internal.impl.dv.util.Base64;

import org.scantegrity.common.ballotstandards.electionSpecification.ElectionSpecification;
import org.w3c.dom.Document;

import org.scantegrity.common.Util;
import org.scantegrity.engine.ioExample.MeetingOneIn;


/**
* This code was edited or generated using CloudGarden's Jigloo
* SWT/Swing GUI Builder, which is free for non-commercial
* use. If Jigloo is being used commercially (ie, by a corporation,
* company or business for any purpose whatever) then you
* should purchase a license for each developer using Jigloo.
* Please visit www.cloudgarden.com for details.
* Use of Jigloo implies acceptance of these licensing terms.
* A COMMERCIAL LICENSE HAS NOT BEEN PURCHASED FOR
* THIS MACHINE, SO JIGLOO OR THIS CODE CANNOT BE USED
* LEGALLY FOR ANY CORPORATE OR COMMERCIAL PURPOSE.
*/
/**
 *	This is the first screen, for the selection of the environment variables: 
 * 	number of ballots, nr of Ds, etc.. 
 */public class Meeting1InputScreen extends JDialog {
	private static final long serialVersionUID = -3555189551108961790L;
	private JPanel jPanel1;
	private JLabel jLabel4;
	private JButton jButtonPartitions;
	private JTextField jtfPartitions;
	private JLabel jLabelPartitions;
	private JLabel jLabelElectionSpecification;
	private JButton jbLoad;
	private JButton jsSave;
	private JButton jbES;
	private JTextField jtfES;
	private JTextField jtfNoDs;
	private JLabel jLabel5;
	private JTextField jtfNoB;
	private JTextField jtfC;
	private JLabel jLabel3;

	final JFileChooser fc = new JFileChooser();

	String c = null;
	int noB = 0;
	int noDs = 0;
	String es = null;
	String partitions = null;

	String pathToM1In="";
	

	/**
	* Auto-generated main method to display this JFrame
	*/
	public static void main(String[] args) {
		Meeting1InputScreen inst = new Meeting1InputScreen("m1in.xml");
		inst.setVisible(true);
	}
	
	public Meeting1InputScreen(String publicDir) {
		super();
		setModal(true);
		this.pathToM1In=publicDir;//+"/MeetingOneIn.xml";
		fc.setCurrentDirectory(new File(pathToM1In).getParentFile());
		initGUI();
		try {
			parse(new File(pathToM1In));
		} catch (Exception e) {
			//e.printStackTrace();
		}
	}
	
	private void initGUI() {
		try {
			setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
			this.addWindowListener(new WindowAdapter() {
				public void windowClosing(WindowEvent evt) {
					rootWindowClosing(evt);
				}
			});
			{
				jPanel1 = new JPanel();
				getContentPane().add(jPanel1, BorderLayout.CENTER);
				jPanel1.setPreferredSize(new java.awt.Dimension(392, 167));
				{
					jLabel3 = new JLabel();
					jPanel1.add(jLabel3);
					jLabel3.setText("Public Constant");
				}
				{
					jtfC = new JTextField();
					jPanel1.add(jtfC);
					jtfC.setPreferredSize(new java.awt.Dimension(262, 20));
				}
				{
					jLabel4 = new JLabel();
					jPanel1.add(jLabel4);
					jLabel4.setText("Number Of Ballots");
				}
				{
					jtfNoB = new JTextField();
					jPanel1.add(jtfNoB);
					jtfNoB.setPreferredSize(new java.awt.Dimension(60, 20));
				}
				{
					jLabel5 = new JLabel();
					jPanel1.add(jLabel5);
					jLabel5.setText("Number Of D Tables");
				}
				{
					jtfNoDs = new JTextField();
					jPanel1.add(jtfNoDs);
					jtfNoDs.setPreferredSize(new java.awt.Dimension(60, 20));
				}
				{
					jLabelElectionSpecification = new JLabel();
					jPanel1.add(jLabelElectionSpecification);
					jLabelElectionSpecification.setText("ElectionSpec");
					jLabelElectionSpecification.setPreferredSize(new java.awt.Dimension(79, 14));
				}
				{
					jtfES = new JTextField("ElectionSpec.xml");
					jPanel1.add(jtfES);
					jtfES.setPreferredSize(new java.awt.Dimension(207, 20));
					jtfES.setEditable(true);
				}
				{
					jbES = new JButton();
					jPanel1.add(jbES);
					jbES.setText("Browse");
					jbES.addActionListener(new ActionListener() {
						public void actionPerformed(ActionEvent evt) {
							int rv = fc.showOpenDialog(new JFrame(
							"Choose the ELection Specification"));
							if (rv == JFileChooser.APPROVE_OPTION) {
								jtfES.setText(fc.getSelectedFile().getAbsolutePath());
							}
						}
					});
				}
				{
					jLabelPartitions = new JLabel();
					jPanel1.add(jLabelPartitions);
					jLabelPartitions.setText("Partitions");
					jLabelPartitions.setPreferredSize(new java.awt.Dimension(79, 14));
				}
				{
					jtfPartitions = new JTextField("partitions.xml");
					jPanel1.add(jtfPartitions);
					jtfPartitions.setEditable(true);
					jtfPartitions
						.setPreferredSize(new java.awt.Dimension(207, 20));
				}
				{
					jButtonPartitions = new JButton();
					jPanel1.add(jButtonPartitions);
					jButtonPartitions.setText("Browse");
					jButtonPartitions.addActionListener(new ActionListener() {
						public void actionPerformed(ActionEvent evt) {
							int rv = fc.showOpenDialog(new JFrame(
								"Choose the Partitions file"));
							if (rv == JFileChooser.APPROVE_OPTION) {
								jtfPartitions.setText(fc.getSelectedFile()
									.getAbsolutePath());
							}
						}
					});
				}
				{
					jsSave = new JButton();
					jPanel1.add(jsSave);
					jsSave.setText("Save");
					jsSave.addActionListener(new ActionListener() {
						public void actionPerformed(ActionEvent evt) {
							try {
								save();
							} catch (Exception e) {
								JOptionPane.showMessageDialog(null,e.getMessage(), "alert", JOptionPane.ERROR_MESSAGE);
								return;
							}
							dispose();
						}
					});
				}
				{
					jbLoad = new JButton();
					jPanel1.add(jbLoad);
					jbLoad.setText("Cancel");
					jbLoad.addActionListener(new ActionListener() {
						public void actionPerformed(ActionEvent evt) {
							rootWindowClosing(null);
							//load();
						}
					});
				}
			}
			pack();
			this.setSize(400, 192);
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	
	/**
	 * Generates the MeetingOneIn XML with the election settings.   
	 * @throws Exception
	 */
	private void write(String file) throws Exception {
		MeetingOneIn.write(es,noB,noDs,c.getBytes(), partitions, file);
	}
	
	/**
	 * Loads a preset MeetingOneIn XMLs 
	 * @throws Exception
	 */
	private void parse(File file) throws Exception {
		Document doc = Util.DomParse(file);
		jtfES.setText(doc.getElementsByTagName("electionSpec").item(0).getFirstChild().getNodeValue());
		jtfNoB.setText(doc.getElementsByTagName("noBallots").item(0).getFirstChild().getNodeValue());
		jtfNoDs.setText(doc.getElementsByTagName("noDs").item(0).getFirstChild().getNodeValue());
		jtfC.setText(new String(Base64.decode(doc.getElementsByTagName("constant").item(0).getFirstChild().getNodeValue())));
	}
	
	/**
	 * Loads MeetingOneIn from a file and fills in the coresponding fields
	 *
	 */
	private void load() {
		try {
			fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
			fc.setSelectedFile(new File(pathToM1In));
		    fc.setVisible(true);
		    int retVal = fc.showOpenDialog(this);
		    
		    if (retVal == JFileChooser.APPROVE_OPTION)
		    {
		    	File f=fc.getSelectedFile();
		    	pathToM1In=f.getAbsolutePath();
		    	parse(f);
		    }
		    else
		    {
		        return;
		    }			
		} catch (Exception e) {
			e.printStackTrace();
		}		
	}
	
	private void save() throws Exception {
		c = jtfC.getText().trim();
		if (c.length() < 16) {
			while (c.length()<16)
				c=c+" ";
			//throw new Exception("The public constant has to have 16 chars. Is has "+c.length());								
		}
		if (c.length() > 16) {
			c=c.substring(0,16);
		}
		
		try {
			noB = Integer.parseInt(jtfNoB.getText());
			if (noB < 1 )
				throw new Exception("");
		} catch(Exception e) {
			throw new Exception("Numbe of ballots must be an integer between > 0");																
		}
		try {
			noDs = Integer.parseInt(jtfNoDs.getText());
			if (noDs < 1)
				throw new Exception("");
		} catch(Exception e) {
			throw new Exception("Numbe of D tables must be an integer between 1 and 20");																
		}
		try {
			if (new File(jtfES.getText()).isAbsolute()) {			
				new ElectionSpecification(jtfES.getText());
			} else {
				new ElectionSpecification(new File(pathToM1In).getParent()+Util.fileSeparator+jtfES.getText());				
			}
			es=jtfES.getText();				
		} catch (Exception e) {
			throw new Exception("Invalid ElectionSpecification file ");																			
		}

		try {
			if (new File(jtfPartitions.getText()).isAbsolute()) {
				Util.DomParse(jtfPartitions.getText());
			} else {
				Util.DomParse(new File(pathToM1In).getParent()+Util.fileSeparator+jtfPartitions.getText());				
			}			
			partitions=jtfPartitions.getText();
		} catch (Exception e) {
			throw new Exception("Invalid ElectionSpecification file ");																			
		}

		
    	try {
			write(pathToM1In);
		} catch (Exception e) {
			JOptionPane.showMessageDialog(null, "Error saving "+pathToM1In, "alert", JOptionPane.ERROR_MESSAGE);				
			return;
		}
		rootWindowClosing(null);
	}
	
	private void rootWindowClosing(WindowEvent evt) {
		this.setVisible(false);
		this.dispose();
	}
}
