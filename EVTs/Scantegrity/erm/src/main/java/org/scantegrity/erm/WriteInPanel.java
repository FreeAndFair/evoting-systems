package org.scantegrity.erm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.image.BufferedImage;
import java.util.Vector;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.ImageIcon;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextField;
import javax.swing.border.TitledBorder;

import org.apache.commons.lang.StringUtils;

public class WriteInPanel extends JPanel {

	private static final long serialVersionUID = 1L;
	private JList jList = null;
	private DefaultListModel listModel = null;
	private JScrollPane jScrollPane = null;
	private JPanel textPanel = null;
	private JTextField textCandidate = null;
	private JPanel imagePanel = null;
	private JLabel imageLabel = null;
	private Vector<String> c_candidateList = null;
	private WriteInResolver c_resolver = null;  //  @jve:decl-index=0:
	private BufferedImage c_writeInImage = null;
	private WriteInLoaderThread c_loader = null;  //  @jve:decl-index=0:
	private JPanel headerPanel = null;
	private JLabel headerLabel = null;
	private String c_contestName = null;
	private String c_rankName = null;
	private boolean c_hadWriteins = false;

	/**
	 * This is the default constructor
	 */
	public WriteInPanel(WriteInResolver p_resolver) {
		super();
		c_resolver = p_resolver;
		initialize();
		
	}

	/**
	 * This method initializes this
	 * 
	 * @return void
	 */
	private void initialize() {
		listModel = new DefaultListModel();
		
		c_candidateList = new Vector<String>();
		
		this.setSize(538, 336);
		this.setLayout(new BorderLayout());
		this.add(getJScrollPane(), BorderLayout.WEST);
		this.add(getTextPanel(), BorderLayout.SOUTH);
		this.add(getImagePanel(), BorderLayout.CENTER);
		this.add(getHeaderPanel(), BorderLayout.NORTH);
		c_loader = new WriteInLoaderThread();
		c_loader.start();
	}

	/**
	 * This method initializes jList	
	 * 	
	 * @return javax.swing.JList	
	 */
	private JList getJList() {
		if (jList == null) {
			jList = new JList();
			jList.setFont(new Font(null, Font.PLAIN, 22));
			jList.setModel(listModel);
			MouseListener l_mouseListener = new MouseAdapter() {
			     public void mouseClicked(MouseEvent e) {
			         if (e.getClickCount() == 2) {
			             int index = jList.locationToIndex(e.getPoint());
			             AddVote((String) jList.getModel().getElementAt(index));
			          }
			     }
			};
			jList.addMouseListener(l_mouseListener);
		}
		return jList;
	}

	/**
	 * This method initializes jScrollPane	
	 * 	
	 * @return javax.swing.JScrollPane	
	 */
	private JScrollPane getJScrollPane() {
		if (jScrollPane == null) {
			jScrollPane = new JScrollPane();
			jScrollPane.setBorder(BorderFactory.createTitledBorder(null, "Candidate List", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			jScrollPane.setViewportView(getJList());
		}
		return jScrollPane;
	}

	/**
	 * This method initializes textPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getTextPanel() {
		if (textPanel == null) {
			textPanel = new JPanel();
			textPanel.setLayout(new BoxLayout(getTextPanel(), BoxLayout.X_AXIS));
			textPanel.setBorder(BorderFactory.createTitledBorder(null, "Resolve Candidate", TitledBorder.LEFT, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			textPanel.add(getTextCandidate(), null);
		}
		return textPanel;
	}

	/**
	 * This method initializes textCandidate	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	private JTextField getTextCandidate() {
		if (textCandidate == null) {
			textCandidate = new JTextField();
			textCandidate.setFont(new Font(null, Font.PLAIN, 22));
			textCandidate.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					AddVote(textCandidate.getText());
				}
			});
		}
		return textCandidate;
	}
	
	public void AddVote(String p_name)
	{
		if( p_name.trim().isEmpty() )
			return;
		if( !c_candidateList.contains(p_name) )
		{
			int l_res = JOptionPane.NO_OPTION;
			for( int x = 0; x < c_candidateList.size() && l_res != JOptionPane.YES_OPTION; x++ )
			{
				if( c_candidateList.get(x).toLowerCase() == p_name.toLowerCase() || StringUtils.getLevenshteinDistance(c_candidateList.get(x), p_name) <= 2 )
				{
					l_res = JOptionPane.showConfirmDialog(getParent(), "Do you mean " + c_candidateList.get(x) + "?","Confirm Match", JOptionPane.YES_NO_OPTION  );
					if( l_res == JOptionPane.YES_OPTION )
						p_name = c_candidateList.get(x);
				}
			}
		}
		
		if( !c_candidateList.contains(p_name) )
		{
			int l_res = JOptionPane.showConfirmDialog(getParent(), "Candidate \"" + p_name + "\" is not in list, would you like to add?", "Confirm Add", JOptionPane.YES_NO_OPTION);
			if( l_res != JOptionPane.YES_OPTION )
				return;
			else
			{
				c_resolver.AddCandidate(p_name);
			}
		}
		c_resolver.Resolve(p_name);
		textCandidate.setText("");
		textCandidate.requestFocusInWindow();
		//Add vote for candidate
		synchronized(c_loader)
		{
			c_loader.notify();
		}
	}

	/**
	 * This method initializes imagePanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getImagePanel() {
		if (imagePanel == null) {
			imageLabel = new JLabel();
			imageLabel.setText("");
			imagePanel = new JPanel();
			imagePanel.setLayout(new BoxLayout(getImagePanel(), BoxLayout.X_AXIS));
			imagePanel.setBorder(BorderFactory.createTitledBorder(null, "Image", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			imagePanel.add(imageLabel, null);
		}
		return imagePanel;
	}
	
	private void UpdateState()
	{
		DefaultListModel l_model = new DefaultListModel();
		for(String l_candidate : c_candidateList)
		{
			l_model.addElement(l_candidate);
		}
		jList.setModel(l_model);
		headerLabel.setFont(new Font(null, Font.PLAIN, 22));
		headerLabel.setText(c_contestName + " RANK " + c_resolver.getRank());
		imageLabel.setIcon(new ImageIcon(c_writeInImage));
	}
	
	//Inner class to load write-ins for resolution
	private class WriteInLoaderThread extends Thread
	{
		public void run()
		{
			while(true)
			{
				if( !c_resolver.next() )
				{
					if( c_hadWriteins )
					{
						JOptionPane.showMessageDialog(getParent(), "Write-in resolution complete");
						c_hadWriteins = false;
					}
					try {
						synchronized(this)
						{
							Thread.sleep(2000);
						}
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					continue;
				}
				c_hadWriteins = true;
				c_candidateList = c_resolver.getCandidates();
				c_writeInImage = c_resolver.getImage();
				c_contestName = c_resolver.getContestName();
				c_rankName = "" + c_resolver.getRank(); 
				UpdateState();
				//Wait for user to resolve write-in
				try {
					synchronized(this)
					{
						this.wait();
					}
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
	}

	/**
	 * This method initializes headerPanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JPanel getHeaderPanel() {
		if (headerPanel == null) {
			headerLabel = new JLabel();
			headerLabel.setText("Contest: ");
			headerPanel = new JPanel();
			headerPanel.setLayout(new GridBagLayout());
			headerPanel.add(headerLabel, new GridBagConstraints());
		}
		return headerPanel;
	}

}  //  @jve:decl-index=0:visual-constraint="10,10"
