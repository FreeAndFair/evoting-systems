package uk.ac.surrey.pav.administrator;

import java.awt.Component;
import java.awt.event.ActionEvent;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.PrintStream;
import java.security.PrivateKey;
import java.sql.Date;
import java.text.DateFormat;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;

import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JTree;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeNode;
import javax.swing.tree.TreePath;

import uk.ac.surrey.pav.administrator.treenodes.AuditMachine;
import uk.ac.surrey.pav.administrator.treenodes.AuditMachineNode;
import uk.ac.surrey.pav.administrator.treenodes.Booth;
import uk.ac.surrey.pav.administrator.treenodes.BoothNode;
import uk.ac.surrey.pav.administrator.treenodes.Candidate;
import uk.ac.surrey.pav.administrator.treenodes.ChildRemovableTreeNode;
import uk.ac.surrey.pav.administrator.treenodes.Election;
import uk.ac.surrey.pav.administrator.treenodes.ElectionNode;
import uk.ac.surrey.pav.administrator.treenodes.Race;
import uk.ac.surrey.pav.administrator.treenodes.Root;
import uk.ac.surrey.pav.administrator.treenodes.Teller;
import uk.ac.surrey.pav.administrator.treenodes.TellerNode;
import uk.ac.surrey.pav.ballotform.BallotForm;
import uk.ac.surrey.pav.ballotform.BallotFormPaper;
import uk.ac.surrey.pav.common.interfaces.CSVable;
import uk.ac.surrey.pav.common.interfaces.SQLable;

/**
 * A GUI used to set up one or more elections
 * 
 * @author David Lundin
 * 
 */
public class VisualAdministrator extends JFrame {

	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * The Administrator that holds all the data about the election
	 */
	private Root rootNode = null;

	private JPanel jContentPane = null; // @jve:decl-index=0:visual-constraint="10,10"

	private JTree jTreeElection = null;

	private JButton jButtonAdd = null;

	private JButton jButtonEdit = null;

	private JButton jButtonDelete = null;

	private JButton jButtonCreate = null;

	private JButton jButtonSave = null;

	private JButton jButtonRestore = null;

	private JButton jButtonCreateSQL = null;

	/**
	 * This method initializes jTreeElection
	 * 
	 * @return javax.swing.JTree
	 */
	private JTree getJTreeElection() {
		if (jTreeElection == null) {
			jTreeElection = new JTree(new DefaultTreeModel(rootNode));
			jTreeElection.setBounds(new java.awt.Rectangle(14, 16, 602, 525));
		}
		return jTreeElection;
	}

	/**
	 * This method initializes jButtonAdd
	 * 
	 * @return javax.swing.JButton
	 */
	private JButton getJButtonAdd() {
		if (jButtonAdd == null) {
			jButtonAdd = new JButton();
			jButtonAdd.setBounds(new java.awt.Rectangle(630, 15, 106, 46));
			jButtonAdd.setToolTipText("Add child to selected node");
			jButtonAdd.setText("Add");
			jButtonAdd.addActionListener(new ButtonAddHandler(this));
		}
		return jButtonAdd;
	}

	/**
	 * This method initializes jButtonEdit
	 * 
	 * @return javax.swing.JButton
	 */
	private JButton getJButtonEdit() {
		if (jButtonEdit == null) {
			jButtonEdit = new JButton();
			jButtonEdit.setBounds(new java.awt.Rectangle(630, 75, 106, 46));
			jButtonEdit.setToolTipText("Edit selected node");
			jButtonEdit.setText("Edit");
			jButtonEdit.addActionListener(new ButtonEditHandler(this));
		}
		return jButtonEdit;
	}

	private JButton getJButtonDelete() {
		if (jButtonDelete == null) {
			jButtonDelete = new JButton();
			jButtonDelete.setBounds(new java.awt.Rectangle(630, 135, 106, 46));
			jButtonDelete.setToolTipText("Delete selected node");
			jButtonDelete.setText("Delete");
			jButtonDelete.addActionListener(new ButtonDeleteHandler(this));
		}
		return jButtonDelete;
	}

	/**
	 * This method initializes jButtonCreate
	 * 
	 * @return javax.swing.JButton
	 */
	private JButton getJButtonCreate() {
		if (jButtonCreate == null) {
			jButtonCreate = new JButton();
			jButtonCreate.setBounds(new java.awt.Rectangle(630, 495, 106, 46));
			jButtonCreate.setToolTipText("Outputs a comma separated value (CSV) file for the printing of the ballot forms");
			jButtonCreate.setText("Ballot Forms");
			jButtonCreate.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					createBallotForms();

				}
			});
		}
		return jButtonCreate;
	}

	/**
	 * This method initializes jButtonSave	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonSave() {
		if (jButtonSave == null) {
			jButtonSave = new JButton();
			jButtonSave.setBounds(new java.awt.Rectangle(630,195,106,46));
			jButtonSave.setToolTipText("Save the tree to a file");
			jButtonSave.setText("Save tree");
			jButtonSave.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					saveRoot();
					
				}
			});
		}
		return jButtonSave;
	}

	/**
	 * This method initializes jButtonRestore	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonRestore() {
		if (jButtonRestore == null) {
			jButtonRestore = new JButton();
			jButtonRestore.setBounds(new java.awt.Rectangle(630,255,106,46));
			jButtonRestore.setToolTipText("Restore the tree from a file");
			jButtonRestore.setText("Restore tree");
			jButtonRestore.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {

					loadRoot();
					
				}
			});
		}
		return jButtonRestore;
	}

	/**
	 * This method initializes jButtonCreateSQL	
	 * 	
	 * @return javax.swing.JButton	
	 */
	private JButton getJButtonCreateSQL() {
		if (jButtonCreateSQL == null) {
			jButtonCreateSQL = new JButton();
			jButtonCreateSQL.setBounds(new java.awt.Rectangle(630,435,106,46));
			jButtonCreateSQL.setToolTipText("Outputs a file with SQL INSERT statements used to create the database");
			jButtonCreateSQL.setText("Entity SQL");
			jButtonCreateSQL.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					
					JFileChooser jfc = new JFileChooser();
					if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
						
						try {
							
							FileOutputStream fos;
							fos = new FileOutputStream(jfc.getSelectedFile());
							PrintStream p = new PrintStream(fos);
							p.print(createSQLFromChildren(rootNode));
							p.close();

					    } catch (IOException ex) {
					    	ex.printStackTrace();
					    }

					}

				}
			});
		}
		return jButtonCreateSQL;
	}

	/**
	 * Simply sets up a visual administrator instance.
	 * 
	 * @param args
	 */
	public static void main(String[] args) {
		// Instantiate the visual administrator and show
		VisualAdministrator vAdmin = new VisualAdministrator();
		vAdmin.setVisible(true);
	}

	/**
	 * This is the default constructor
	 */
	public VisualAdministrator() {
		super();
		initialize();
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		this.rootNode = new Root();
		this.setSize(758, 590);
		this.setContentPane(getJContentPane());
		this.setTitle("Election Administrator");
		this.addWindowListener(new java.awt.event.WindowAdapter() {
			public void windowClosing(java.awt.event.WindowEvent e) {
				// When the window is closed: exit
				System.exit(0);
			}
		});
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
			jContentPane.setSize(new java.awt.Dimension(489, 254));
			jContentPane.setBorder(javax.swing.BorderFactory.createBevelBorder(javax.swing.border.BevelBorder.LOWERED));
			jContentPane.add(getJTreeElection(), null);
			jContentPane.add(getJButtonAdd(), null);
			jContentPane.add(getJButtonEdit(), null);
			jContentPane.add(getJButtonDelete(), null);
			jContentPane.add(getJButtonCreate(), null);
			jContentPane.add(getJButtonSave(), null);
			jContentPane.add(getJButtonRestore(), null);
			jContentPane.add(getJButtonCreateSQL(), null);
			jContentPane.addComponentListener(new java.awt.event.ComponentListener() {
				public void componentResized(java.awt.event.ComponentEvent e) {

					//Resize and move the buttons and whatnot
					int margin = 15;
					int buttonWidth = 8 * 15;
					int buttonHeight = 3 * 15;

					//Resize and move the JTree
					getJTreeElection().setSize(jContentPane.getWidth() - buttonWidth - (3 * margin), jContentPane.getHeight() - (2 * margin));
					getJTreeElection().setLocation(margin, margin);
					
					//Button sizes
					jButtonAdd.setSize(buttonWidth, buttonHeight);
					jButtonEdit.setSize(buttonWidth, buttonHeight);
					jButtonDelete.setSize(buttonWidth, buttonHeight);
					jButtonSave.setSize(buttonWidth, buttonHeight);
					jButtonRestore.setSize(buttonWidth, buttonHeight);
					
					jButtonCreateSQL.setSize(buttonWidth, buttonHeight);
					jButtonCreate.setSize(buttonWidth, buttonHeight);
					
					//Button places
					int buttonLeftEdge = getJTreeElection().getWidth() + (2 * margin);
					jButtonAdd.setLocation(buttonLeftEdge, margin);
					jButtonEdit.setLocation(buttonLeftEdge, jButtonAdd.getLocation().y + jButtonAdd.getHeight() + margin);
					jButtonDelete.setLocation(buttonLeftEdge, jButtonEdit.getLocation().y + jButtonEdit.getHeight() + margin);
					jButtonSave.setLocation(buttonLeftEdge, jButtonDelete.getLocation().y + jButtonDelete.getHeight() + margin);
					jButtonRestore.setLocation(buttonLeftEdge, jButtonSave.getLocation().y + jButtonSave.getHeight() + margin);
					
					jButtonCreate.setLocation(buttonLeftEdge, jContentPane.getHeight() - jButtonCreate.getHeight() - margin);
					jButtonCreateSQL.setLocation(buttonLeftEdge, jContentPane.getHeight() - jButtonCreate.getHeight() - jButtonCreateSQL.getHeight() - (2 * margin));
					
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
	 * Reads in a string name from a visual input box
	 */
	public String getNewName(Component owner, String message) {
		String temp = JOptionPane.showInputDialog(owner, message, "Question", JOptionPane.QUESTION_MESSAGE);
		return temp;
	}

	public Root getRootNode() {
		return rootNode;
	}

	public void setRootNode(Root rootNode) {
		this.rootNode = rootNode;
	}

	class ButtonEditHandler extends ButtonHandler {
		public ButtonEditHandler(VisualAdministrator v) {
			super(v);
		}

		public void actionPerformed(ActionEvent e) {
			TreePath parentPath = jTreeElection.getSelectionPath();
			if (parentPath != null) {
				Object selectedObj = parentPath.getLastPathComponent();
				if (selectedObj instanceof Teller) {
					
					(new NewEntityDialog((Teller)selectedObj)).setVisible(true);
					((DefaultTreeModel) jTreeElection.getModel()).reload((Teller)selectedObj);
					
				} else if (selectedObj instanceof Booth) {
						
					(new NewEntityDialog((Booth)selectedObj)).setVisible(true);
					((DefaultTreeModel) jTreeElection.getModel()).reload((Booth)selectedObj);

				} else if (selectedObj instanceof AuditMachine) {
					
					(new NewEntityDialog((AuditMachine)selectedObj)).setVisible(true);
					((DefaultTreeModel) jTreeElection.getModel()).reload((AuditMachine)selectedObj);

				} else if (selectedObj instanceof Election) {
					
					(new NewElectionDialog((Election)selectedObj)).setVisible(true);
					((DefaultTreeModel) jTreeElection.getModel()).reload((Election)selectedObj);

				} else if (selectedObj instanceof NameEditableEntity) {
					
					String temp = JOptionPane.showInputDialog(jContentPane, "Please enter the new name:", ((NameEditableEntity)selectedObj).getName());
					if(temp.length() > 0) {
						((NameEditableEntity)selectedObj).setName(temp);
						((DefaultTreeModel) jTreeElection.getModel()).reload((TreeNode)selectedObj);
					}
					
				}
			}
		}
	}

	class ButtonDeleteHandler extends ButtonHandler {
		public ButtonDeleteHandler(VisualAdministrator v) {
			super(v);
		}

		public void actionPerformed(ActionEvent e) {
			
			// See if anything is selected in the tree
			TreePath parentPath = jTreeElection.getSelectionPath();
			if (parentPath != null) {
				// Something is selected in the tree
				// Check what is selected
				Object selectedObj = parentPath.getLastPathComponent();
				if (selectedObj instanceof TreeNode) {
					if(((TreeNode)selectedObj).getParent() instanceof ChildRemovableTreeNode) {

						//We can remove these elements
						((ChildRemovableTreeNode)((TreeNode)selectedObj).getParent()).removeChild(selectedObj);
						
						//Update the tree
						((DefaultTreeModel)jTreeElection.getModel()).reload(((TreeNode)selectedObj).getParent());
						
					}
					
				}
			}
		}
		
	}

	class ButtonAddHandler extends ButtonHandler {
		public ButtonAddHandler(VisualAdministrator v) {
			super(v);
		}

		public void actionPerformed(ActionEvent e) {
			// See if anything is selected in the tree
			TreePath parentPath = jTreeElection.getSelectionPath();
			if (parentPath != null) {
				// Something is selected in the tree
				// Check what is selected
				Object selectedObj = parentPath.getLastPathComponent();
				if ((selectedObj instanceof TellerNode)) {
					//We are adding a teller
					
					//A new teller
					Teller newTeller = new Teller((TellerNode)selectedObj);
					
					//Show dialog box
					(new NewEntityDialog(newTeller)).setVisible(true);
					
					//Check if this is properly filled out
					if(newTeller.isProper()) {
						
						//It is so add it to the list
						((TellerNode)selectedObj).addTeller(newTeller);
						
						//Update the tree
						((DefaultTreeModel) jTreeElection.getModel()).reload((TellerNode)selectedObj);
						
					}
					
				} else if ((selectedObj instanceof BoothNode)) {
					//We are adding a booth
					
					//A new booth
					Booth newBooth = new Booth((BoothNode)selectedObj);
					
					//Show dialog box
					(new NewEntityDialog(newBooth)).setVisible(true);
					
					//Check if this is properly filled out
					if(newBooth.isProper()) {
						
						//It is so add it to the list
						((BoothNode)selectedObj).addBooth(newBooth);
						
						//Update the tree
						((DefaultTreeModel) jTreeElection.getModel()).reload((BoothNode)selectedObj);
						
					}

				} else if ((selectedObj instanceof AuditMachineNode)) {
					//We are adding a booth
					
					//A new booth
					AuditMachine newAuditMachine = new AuditMachine((AuditMachineNode)selectedObj);
					
					//Show dialog box
					(new NewEntityDialog(newAuditMachine)).setVisible(true);
					
					//Check if this is properly filled out
					if(newAuditMachine.isProper()) {
						
						//It is so add it to the list
						((AuditMachineNode)selectedObj).addAuditMachine(newAuditMachine);
						
						//Update the tree
						((DefaultTreeModel) jTreeElection.getModel()).reload((AuditMachineNode)selectedObj);
						
					}

				} else if ((selectedObj instanceof ElectionNode)) {

					//The root object
					ElectionNode root = (ElectionNode) selectedObj;
					
					//Create a new election
					Election election = new Election(root);
					
					if(election.isProper()) {

						//Store the election
						root.addElection(election);
						
						//Reload the tree
						((DefaultTreeModel) jTreeElection.getModel()).reload((TreeNode)root);

					}

				} else if (selectedObj instanceof Election) {
					String n = getNewName(this.adapter, "Please enter the name of the race:");
					Election election = (Election) selectedObj;
					Race race = new Race(n, election);

					if (election.hasDuplicatedRace(race)) {
						javax.swing.JOptionPane.showMessageDialog(this.adapter, "The name you have entered is invalid.");
					} else {
						election.addRace(race);
						((DefaultTreeModel) jTreeElection.getModel()).reload(election);
					}
				} else if (selectedObj instanceof Race) {
					String n = getNewName(this.adapter, "Please enter the name of the candidate:");
					Race race = (Race) selectedObj;
					Candidate candidate = new Candidate(n, race);
					if (race.hasDuplicatedCandidate(candidate)) {
						javax.swing.JOptionPane.showMessageDialog(this.adapter, "The name you have entered is invalid.");
					} else {
						race.addCandidate(candidate);
						((DefaultTreeModel) jTreeElection.getModel()).reload((TreeNode)race);
					}
				}
			}
			// ((DefaultTreeModel)jTreeElection.getModel()).nodeStructureChanged(node)
		}
	}

	private StringBuffer createSQLFromChildren(TreeNode node) {
		
		//The result
		StringBuffer result = new StringBuffer();
		
		//If this node is SQLable...
		if(node instanceof SQLable) {
			//...add it's SQL
			result.append(((SQLable)node).toSQL() + "\n");
		}
		
		//If it has children
		for(int x=0; x<node.getChildCount(); x++) {
			result.append(createSQLFromChildren(node.getChildAt(x)));
		}
		
		//Done, return
		return result;
		
	}
	
	/**
	 * Saves the root to file
	 * 
	 */
	private void saveRoot() {
		
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				ObjectOutputStream objectOut = new ObjectOutputStream(new FileOutputStream(jfc.getSelectedFile()));
				objectOut.writeObject(this.rootNode);

		    } catch (IOException e) {
		    	e.printStackTrace();
		    }

		}

	}
	
	/**
	 * Load root from file 
	 *
	 */
	private void loadRoot() {
		
		//Open a file
		JFileChooser jfc = new JFileChooser();
		if(jfc.showOpenDialog(getJContentPane()) == JFileChooser.APPROVE_OPTION) {
			try {
				
				//Load key pair
				ObjectInputStream objectIn = new ObjectInputStream(new FileInputStream(jfc.getSelectedFile()));
				this.rootNode = ((Root)objectIn.readObject());
				jTreeElection.setModel(new DefaultTreeModel(rootNode));

		    } catch (Exception ex) {
		    	ex.printStackTrace();
		    }

		}

	}
	
	/**
	 * Creates ballot forms
	 *
	 */
	private void createBallotForms() {
		
		//Show a creator dialog
		(new BallotFormCreationDialog(this, rootNode)).setVisible(true);

	}


} // @jve:decl-index=0:visual-constraint="10,10"
