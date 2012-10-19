package org.scantegrity.erm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.GridLayout;
import java.awt.Label;
import java.awt.Panel;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.Vector;

import javax.imageio.ImageIO;
import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.DefaultListModel;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JToggleButton;
import javax.swing.border.TitledBorder;

import org.apache.commons.lang.StringUtils;

public class ErrorPanel extends JPanel {

	private static final long serialVersionUID = 1L;
	private JList jList = null;
	private DefaultListModel listModel = null;
	private JScrollPane jScrollPane = null;
	private JPanel textPanel = null;
	private JScrollPane imagePanel = null;
	private JLabel imageLabel = null;
	private ErrorBallotResolver c_resolver = null;  //  @jve:decl-index=0:
	private BufferedImage c_ErrorBallotImage = null;
	private ErrorBallotLoaderThread c_loader = null;  //  @jve:decl-index=0:
	private JPanel headerPanel = null;
	private JLabel headerLabel = null;
	private String c_contestName = null;
	private boolean c_hadErrorBallots = false;
	private Integer[][] c_contestData; 
	private Panel c_buttonPanel = null; 
	private Panel c_errorPanel = null; 
	private JTextArea c_errorTextArea = null;
	private Panel c_buttonGrid = null; 
	private JButton c_continueButton = null; 

	/**
	 * This is the default constructor
	 */
	public ErrorPanel(ErrorBallotResolver p_resolver) {
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
		this.setSize(538, 336);
		this.setLayout(new BorderLayout());
		this.add(getCenterPanel(), BorderLayout.EAST); 
		this.add(getImagePanel(), BorderLayout.CENTER); // ballot image
		this.add(getHeaderPanel(), BorderLayout.NORTH);
		c_loader = new ErrorBallotLoaderThread();
		c_loader.start();
	}

	private Component getCenterPanel() {
		Panel centerPanel = new Panel(); 
		centerPanel.setLayout(new BorderLayout()); 
		centerPanel.add(getErrorsPanel(), BorderLayout.NORTH); 
		centerPanel.add(getButtonPanel(), BorderLayout.SOUTH); 
		return centerPanel;
	}

	private Component getErrorsPanel() {
		if (c_errorPanel == null) { 
			c_errorPanel = new Panel();
			c_errorPanel.setLayout(new BoxLayout(c_errorPanel, BoxLayout.PAGE_AXIS));
			c_errorPanel.add(new JLabel("Voting Errors Found:"));
			if (c_errorTextArea == null) { 
				c_errorTextArea = new JTextArea(); 
			}
			c_errorPanel.add(c_errorTextArea); 
			c_errorPanel.setPreferredSize(new Dimension(200, 150));
		}
		return c_errorPanel;
	}

	private Component getButtonPanel() {
		if (c_buttonPanel == null) {
			c_buttonPanel = new Panel();
			c_buttonPanel.setLayout(new BorderLayout());
			MouseListener l_mouseListener = new MouseAdapter() {
			     public void mouseClicked(MouseEvent e) {
			    	 AddVote();
			     }
			};
			c_continueButton = new JButton("Save and Continue");
			c_continueButton.addMouseListener(l_mouseListener);
			c_buttonPanel.add(c_continueButton, BorderLayout.SOUTH);
		}
		return c_buttonPanel;
	}
	
	public void AddVote() { 
		if (c_continueButton.isEnabled()) { 
			int l_res = JOptionPane.NO_OPTION;
			l_res = JOptionPane.showConfirmDialog(getParent(), "Save new results?", "Confirm Resolve", JOptionPane.YES_NO_OPTION  );
			if( l_res == JOptionPane.YES_OPTION ) {
				Integer[][] p_contestData = c_resolver.getContestData();
				
				int l_elementCount = 0; 
				Component[] elements = c_buttonGrid.getComponents(); 
				for (int i = 0; i < p_contestData.length; i++) { 
					for (int j = 0; j < p_contestData[i].length; j++) {
						if (((JToggleButton) (elements[l_elementCount])).isSelected()) { 
							p_contestData[i][j] = 1; 
						} else {
							p_contestData[i][j] = 0; 
						}
						
						l_elementCount++; 
					}
				}
				c_resolver.Resolve(p_contestData);
				synchronized(c_loader)
				{
					c_loader.notify();
				}
			}
		}
	}

	/**
	 * This method initializes imagePanel	
	 * 	
	 * @return javax.swing.JPanel	
	 */
	private JScrollPane getImagePanel() {
		if (imagePanel == null) {
			imageLabel = new JLabel(); 
			imageLabel.setText("");
			imagePanel = new JScrollPane();
			imagePanel.setBorder(BorderFactory.createTitledBorder(null, "Ballot Image", TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, new Font("Dialog", Font.BOLD, 12), new Color(51, 51, 51)));
			imagePanel.getViewport().add(imageLabel, null);
		}
		return imagePanel;
	}
	
	private void UpdateState() {
		headerLabel.setFont(new Font(null, Font.PLAIN, 22));
		headerLabel.setText(c_contestName);
		imageLabel.setIcon(new ImageIcon(c_ErrorBallotImage));
		
		/* Debug * / 
		try {
			ImageIO.write(c_ErrorBallotImage,"png",new File("error_ballot_" +  + "".png"));
			System.out.println(c_ErrorBallotImage.getWidth());
			System.out.println(c_ErrorBallotImage.getHeight()); 
		} catch (IOException e) {
			//
		}
		/* End Debug */
		
		imagePanel.revalidate(); 

		if (c_buttonGrid != null) { 
			c_buttonGrid.removeAll();
			//c_buttonGrid = null;
		} else { 
			c_buttonGrid = new Panel(); 
		}
		
		Integer[][] l_contestData = c_resolver.getContestData(); 
		c_buttonGrid.setLayout(new GridLayout(l_contestData.length, l_contestData[0].length));
		for (int i = 0; i < l_contestData.length; i++) { 
			for (int j = 0; j < l_contestData[i].length; j++) {
				boolean selected = true; 
				if (l_contestData[i][j] == 0) {
					selected = false; 
				}
				
				c_buttonGrid.add(new JToggleButton("", selected)); 
			}
		}
		
		c_buttonPanel.add(c_buttonGrid, BorderLayout.CENTER); 
	}
	
	//Inner class to load write-ins for resolution
	private class ErrorBallotLoaderThread extends Thread
	{
		public void run()
		{
			while(true)
			{
				if( !c_resolver.next() )
				{
					if( c_hadErrorBallots )
					{
						JOptionPane.showMessageDialog(getParent(), "Ballot errors resolution complete");
						c_hadErrorBallots = false;
						if (c_continueButton != null) { 
							c_continueButton.setEnabled(false);
						}
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
				
				c_hadErrorBallots = true;
				c_contestData = c_resolver.getContestData();
				c_ErrorBallotImage = c_resolver.getImage();
				c_contestName = c_resolver.getContestName();
				c_errorTextArea.setText(""); 
				for (String error: c_resolver.getErrorStrings()) { 
					c_errorTextArea.append(error + "\n"); 
				}
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
