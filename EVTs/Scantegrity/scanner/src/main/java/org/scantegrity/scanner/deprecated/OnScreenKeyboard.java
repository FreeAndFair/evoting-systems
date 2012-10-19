/*
 * @(#)OnScreenKeyboard.java.java
 *  
 * Copyright (C) 2008-2009 Scantegrity Project
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package org.scantegrity.scanner.deprecated;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.GridLayout;
import java.awt.Point;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Arrays;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTextField;
import javax.swing.SwingConstants;

/**
 * @author John Conway
 *
 */
public class OnScreenKeyboard extends JDialog implements ActionListener
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -7633434637654379213L;


	private static String c_rows[][] = {
		{ "1", "2", "3", "4", "5", "6", "7", "8", "9", "0" },
		{ "Q", "W", "E", "R", "T", "Y", "U", "I", "O", "P" },
		{ "A", "S", "D", "F", "G", "H", "J", "K", "L" },
		{ "Z", "X", "C", "V", "B", "N", "M", "Shift" },
		{ "Backspace", "Space", "Enter"}
	};  //  @jve:decl-index=0:
	
	
	private Font c_font = null;
	private boolean secure = false;
	
	private String c_buf = "";  //  @jve:decl-index=0:
	private char blankChar = '*';
	
	
	private JTextField c_textField = null;
	private JPanel c_panel = null;
	private JButton c_enter = null;
	private JButton c_shift = null;
	private JButton c_buttons[][] = null;
	private boolean c_shifted = false;
	private boolean c_secure = false;
	
	public OnScreenKeyboard(JFrame p_parent, String p_title)
	{
		this(p_parent, p_title, false);
	}
	
	
	public OnScreenKeyboard(JFrame p_parent, String p_title, boolean p_secure) {
		super(p_parent, p_title, true);
				
	    if (p_parent != null) {
	        Dimension parentSize = p_parent.getSize(); 
	        Point p = p_parent.getLocation(); 
	        setLocation(p.x + parentSize.width / 20, p.y + parentSize.height / 10);
	    }			
	    
	    c_secure = p_secure;
	    	    
		c_font = new Font("Courier", 1, 48) ;				
		
		JLabel l_title = new JLabel(p_title);
		l_title.setFont(c_font);
		c_textField = new JTextField("");
		c_textField.setFont(c_font);
		c_textField.setHorizontalAlignment(JTextField.CENTER);
		//Each row get's it's own JPanel row.
		c_panel = new JPanel(new GridLayout(c_rows.length+2, 0));
		c_panel.add(l_title);
		c_panel.add(c_textField);
		//c_panel.
		int l_minx = c_textField.getPreferredSize().width;
		int l_miny = c_textField.getPreferredSize().height*2;
		int l_x = 0, l_y = 0;
		c_buttons = new JButton[c_rows.length][];
		for (int l_i = 0; l_i < c_rows.length; l_i++)
		{
			c_buttons[l_i] = new JButton[c_rows[l_i].length];
			JPanel l_panel = new JPanel();
			l_x = 0;
			for (int l_j = 0; l_j < c_rows[l_i].length; l_j++)
			{
				JButton l_tmp = createButton(c_rows[l_i][l_j]);
				l_x += l_tmp.getPreferredSize().width+15;
				l_y = Math.max(l_tmp.getPreferredSize().height, l_y);
				l_panel.add(l_tmp);
				c_buttons[l_i][l_j] = l_tmp;
			}
			l_minx = Math.max(l_x, l_minx);
			l_miny += l_y+15;
			c_panel.add(l_panel);
		}
	    setDefaultCloseOperation(DISPOSE_ON_CLOSE);
		c_enter.addActionListener(this);	    
		setSize(l_minx, l_miny);
		getContentPane().add(c_panel);
		setVisible(true);
	}	
	
	private JButton createButton(String p_msg)
	{
		JButton l_button = new JButton();
		l_button.setActionCommand(p_msg + " Command");
		l_button.setHorizontalAlignment(SwingConstants.CENTER);
		l_button.setFont(c_font);
		
		//Is this a special button?
		if (p_msg.equals("Shift"))
		{
			l_button.setPreferredSize(new Dimension(200,75));
			l_button.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					Shift();
				}
			});	
			c_shift = l_button;
			
		}
		else if (p_msg.equals("Backspace"))
		{
			l_button.setPreferredSize(new Dimension(200,75));
			p_msg = "Back";
			l_button.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					Backspace();
				}
			});				
		}
		else if (p_msg.equals("Space"))
		{
			l_button.setPreferredSize(new Dimension(400,75));
			p_msg = "    " + p_msg + "    ";
			l_button.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					Append(" ");
				}
			});						
		}
		else if (p_msg.equals("Enter"))
		{
			l_button.setPreferredSize(new Dimension(200,75));
			c_enter = l_button;
		}
		else
		{
			l_button.setPreferredSize(new Dimension(75,75));
			p_msg = p_msg.toLowerCase();
			final String l_msg = new String(p_msg.toLowerCase());
			l_button.addActionListener(new java.awt.event.ActionListener() {
				public void actionPerformed(java.awt.event.ActionEvent e) {
					Append(l_msg);
				}
			});			
		}
		
		l_button.setText(p_msg);
		//l_button.setMinimumSize(new Dimension(36,50));
		//l_button.setSize(new Dimension(36,50));
		l_button.setEnabled(true);
		l_button.setFocusable(false);
		return l_button;
	}
	
	/**
	 * 
	 */
	protected void Shift()
	{
		// TODO Auto-generated method stub
		c_shifted = (c_shifted) ? false:true;
		c_shift.setSelected(c_shifted);
		c_shift.repaint();
		for (int l_i = 0; l_i < c_rows.length; l_i++)
		{
			for (int l_j = 0; l_j < c_rows[l_i].length; l_j++)
			{
				JButton l_c = c_buttons[l_i][l_j]; 
				if (l_c.getText().length() == 1)
				{
					if (c_shifted) l_c.setText(l_c.getText().toUpperCase());
					else l_c.setText(l_c.getText().toLowerCase());
				}
			}
		}		
	}

	/**
	 * 
	 */
	protected void Backspace()
	{
		if ( c_buf.length() > 0 )
		{
			c_buf = c_buf.substring(0, c_buf.length()-1) ;
		}
		if ( c_secure )
		{
			char[] l_c = new char[c_buf.length()];
	        Arrays.fill(l_c, '*') ;
	        c_textField.setText(String.valueOf(l_c)) ;
		} else {
			c_textField.setText(c_buf) ;
		}		
	}

	private void Append(String p_msg)
	{
		if (c_shifted) p_msg = p_msg.toUpperCase();
		c_buf += p_msg;
		if (c_secure)
		{
			char[] l_c = new char[c_buf.length()-1];
			Arrays.fill(l_c, '*');
			c_textField.setText(new String(l_c) + p_msg);
		}
		else
		{
			c_textField.setText(c_buf);			
		}
	}

	public String getBuffer()
	{
		return c_buf;
	}
	
	/* (non-Javadoc)
	 * @see java.awt.event.ActionListener#actionPerformed(java.awt.event.ActionEvent)
	 */
	@Override
	public void actionPerformed(ActionEvent p_e)
	{
		setVisible(false);
		dispose();		
	}

}
