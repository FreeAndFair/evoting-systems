/*
 * Scantegrity - Successor to Punchscan, a High Integrity Voting System
 * Copyright (C) 2006  Richard Carback, David Chaum, Jeremy Clark, 
 * Aleks Essex, Stefan Popoveniuc, and Jeremy Robin
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

package org.scantegrity.scanner;
import java.awt.BorderLayout;

import java.awt.Color;
import java.awt.Cursor;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.GridLayout;
import java.awt.Rectangle;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionAdapter;
import java.awt.event.MouseMotionListener;
import java.awt.font.FontRenderContext;
import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import java.awt.image.AffineTransformOp;
import java.awt.image.BufferedImage;
import java.io.File;
import java.util.Vector;

import javax.imageio.ImageIO;
import javax.swing.JButton;

import javax.swing.BorderFactory;
import javax.swing.ImageIcon;
import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.WindowConstants;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.SwingConstants;


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
public class ImagePanel extends javax.swing.JPanel implements MouseListener,MouseMotionListener {
	private static final long serialVersionUID = 1L;
	private JLabel imageCoordinatesLabel;
	private JButton jButtonZoomIn;
	private JButton jButtonZoomOut;
	private JPanel jPanelZoom;
	private JPanel imageStatus;
	private JLabel imageOnLabel;
	private JScrollPane jScrollPane;
	private JLabel fileNameLabel;
	private JButton browseButton;
	private JPanel browsePanel;
	final JFileChooser fc = new JFileChooser(".");
	Vector<ActionListener> objectsThatAreListeningToThis = new Vector<ActionListener>();
	
	private Vector<Cluster> clusters = new Vector<Cluster>();
	
	BufferedImage image = null;
	BufferedImage displayedImage = null;
	double zoom = 1.0;
	
	double dpi=1;
	/**
	* Auto-generated main method to display this 
	* JPanel inside a new JFrame.
	*/
	public static void main(String[] args) {
		JFrame frame = new JFrame();
		frame.getContentPane().add(new ImagePanel());
		frame.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		frame.pack();
		frame.setVisible(true);
	}
	
	public ImagePanel() {
		super();
		initGUI();
	}
	
	public ImagePanel(BufferedImage img) {
		super();
		this.image = img;
		initGUI();
	}
	
	private void initGUI() {
		try {
			{
				BorderLayout imagePanelLayout = new BorderLayout();
				this.setLayout(imagePanelLayout);
				this.setPreferredSize(new java.awt.Dimension(247, 66));
				{
					browsePanel = new JPanel();
					BorderLayout browsePanelLayout = new BorderLayout();
					browsePanelLayout.setHgap(5);
					this.add(browsePanel, BorderLayout.NORTH);
					browsePanel.setLayout(browsePanelLayout);
					{
						browseButton = new JButton();
						browsePanel.add(browseButton, BorderLayout.WEST);
						browseButton.setText("Browse");
						browseButton.addActionListener(new ActionListener() {
							public void actionPerformed(ActionEvent evt) {
								browseButtonActionPerformed();
							}
						});
					}
					{
						fileNameLabel = new JLabel();
						browsePanel.add(fileNameLabel, BorderLayout.CENTER);
						fileNameLabel.setText("No file selected");
					}
					{
						jPanelZoom = new JPanel();
						browsePanel.add(jPanelZoom, BorderLayout.EAST);
						{
							jButtonZoomOut = new JButton();
							jPanelZoom.add(jButtonZoomOut);
							jButtonZoomOut.setText("-");
							jButtonZoomOut
								.addActionListener(new ActionListener() {
								public void actionPerformed(ActionEvent evt) {
									if (zoom > 0.1)
										zoom-=0.1;
									AffineTransformOp op = new AffineTransformOp(AffineTransform.getScaleInstance(zoom,zoom),AffineTransformOp.TYPE_BILINEAR);
									
									displayedImage = op.filter(image,null);
									imageOnLabel.setIcon(new ImageIcon(displayedImage));
									}
								});
						}
						{
							jButtonZoomIn = new JButton();
							jPanelZoom.add(jButtonZoomIn);
							jButtonZoomIn.setText("+");
							jButtonZoomIn.setAlignmentY(0.0f);
							jButtonZoomIn
								.addActionListener(new ActionListener() {
								public void actionPerformed(ActionEvent evt) {
									if (zoom < 3)
										zoom+=0.1;
									AffineTransformOp op = new AffineTransformOp(AffineTransform.getScaleInstance(zoom,zoom),AffineTransformOp.TYPE_BILINEAR);
									
									displayedImage = op.filter(image,null);
									imageOnLabel.setIcon(new ImageIcon(displayedImage));
								}
								});
						}
					}
				}
				{
					jScrollPane = new JScrollPane();
					this.add(jScrollPane, BorderLayout.CENTER);
					{
						imageOnLabel = new JLabel();
						FlowLayout imageOnLabelLayout = new FlowLayout();
						imageOnLabel.addMouseMotionListener(new MouseMotionAdapter() {
							 public void mouseDragged(MouseEvent e) {
							        //The user is dragging us, so scroll!
							        Rectangle r = new Rectangle(e.getX(), e.getY(), 1, 1);
							        imageOnLabel.scrollRectToVisible(r);		 
								 }							
						});
						imageOnLabel.setAutoscrolls(true);
						imageOnLabel.setBorder(BorderFactory.createLineBorder(Color.BLACK));
						jScrollPane.setViewportView(imageOnLabel);
						imageOnLabel.setVerticalAlignment(SwingConstants.TOP);
//						imageOnLabel.setHorizontalAlignment(SwingConstants.CENTER);
						imageOnLabel.setLayout(imageOnLabelLayout);
						imageOnLabel.setName("Mark Detector");
						imageOnLabel.addMouseListener(this);
						imageOnLabel.addMouseMotionListener(this);
					}
				}
				{
					imageStatus = new JPanel();
					GridLayout imageStatusLayout = new GridLayout(1, 2);
					imageStatusLayout.setHgap(5);
					imageStatusLayout.setColumns(2);
					this.add(imageStatus, BorderLayout.SOUTH);
					imageStatus.setLayout(imageStatusLayout);
					{
						imageCoordinatesLabel = new JLabel();
						imageStatus.add(imageCoordinatesLabel);
						imageCoordinatesLabel.setText("No coordinates");
					}
				}
			}
			if (image != null) {
				imageOnLabel.setIcon(new ImageIcon(image));							
			}			
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	public BufferedImage getImage() {
		return image;
	}

	public void setImage(BufferedImage image) {
		this.image = image;
		repaint();
	}
	
	public void mouseClicked(MouseEvent e) {
		int x = (int)(e.getX()*(1.0/zoom));
		int y = (int)(e.getY()*(1.0/zoom));
		
		for (int i=0;i<objectsThatAreListeningToThis.size();i++) {
			try {
				((ActionListener)objectsThatAreListeningToThis.get(i)).actionPerformed(new ActionEvent(this,0,Integer.toString(image.getRGB(x,y))));
			} catch(ArrayIndexOutOfBoundsException ex) {
				
			}
		}
	}
	
	public void 	mouseEntered(MouseEvent e) {
		 Cursor hourglassCursor = new Cursor(Cursor.CROSSHAIR_CURSOR);
		 setCursor(hourglassCursor);		
	}
	public void 	mouseExited(MouseEvent e) {
		 Cursor hourglassCursor = new Cursor(Cursor.DEFAULT_CURSOR);
		 setCursor(hourglassCursor);		
	}
	
	public void 	mousePressed(MouseEvent e) {
		
	}
	public void 	mouseReleased(MouseEvent e) {
		
	}
	 public void 	mouseDragged(MouseEvent e) {

	 }

	public void mouseMoved(MouseEvent evt) {
		int x = evt.getX();
		int y = evt.getY();
		String coordinatesText = "X" + x + " Y" + y;
		try {
			if (imageOnLabel.getIcon() != null) {
				Color c = new Color(
					((BufferedImage) (((ImageIcon) imageOnLabel
						.getIcon()).getImage()))
						.getRGB(x, y));
				coordinatesText += " R"
					+ c.getRed()
					+ " G"
					+ c.getGreen()
					+ " B"
					+ c.getBlue();
			}
		} catch (ArrayIndexOutOfBoundsException ex) {
		}
		imageCoordinatesLabel
			.setText(coordinatesText);
		
		for (int i=0;i<clusters.size();i++) {
			Cluster c = (Cluster)clusters.get(i);
			if (x>=c.getXmin()*dpi*zoom && x<=c.getXmax()*dpi*zoom && y>=c.getYmin()*dpi*zoom && y<=c.getYmax()*dpi*zoom) {
				imageOnLabel.setToolTipText(c.toString());				
				return;
			}
		}
		imageOnLabel.setToolTipText("");		
		//imageOnLabel.setToolTipText(toolTip);
	}
    
	public void addActionListner(ActionListener a) {
		objectsThatAreListeningToThis.add(a);
	}
	
	public void emphasizeClusters(Vector<Cluster> v,Color color) {		
		clusters.addAll(v);
		BufferedImage duplicate = image;//ImagePanel.duplicate(image);
		Graphics g = duplicate.getGraphics();
		for (int i=0;i<v.size();i++) {
			Cluster c = (Cluster)v.get(i);
			ImagePanel.drawThickLine(c,dpi,g,color);
		}
		AffineTransformOp op = new AffineTransformOp(AffineTransform.getScaleInstance(zoom,zoom),AffineTransformOp.TYPE_BILINEAR);
		
		displayedImage = op.filter(duplicate,null);
		
		imageOnLabel.setIcon(new ImageIcon(displayedImage));		
		this.repaint();
	}

	public static BufferedImage duplicate(BufferedImage img) {
		int[] pixels = img.getRGB(0,0,img.getWidth(),img.getHeight(),null,0,img.getWidth());
		BufferedImage retImg = new BufferedImage(img.getWidth(),img.getHeight(),img.getType());
		retImg.setRGB(0,0,retImg.getWidth(),retImg.getHeight(),pixels,0,retImg.getWidth());
		return retImg;
	}
	
	public static void drawChar(Graphics g,Point2D p,String s,Font f,Color c) {
		Color cb = g.getColor();
		Font fb = g.getFont();
		
		FontRenderContext frc = new FontRenderContext(null,false,false);
		Rectangle2D r = f.getStringBounds(s,frc);
		double w = r.getWidth();
		double h = r.getHeight();
				
		g.setColor(c);
		g.setFont(f);
		g.drawString(s,(int)(p.getX()-(w*0.5)),(int)(p.getY()+(h*0.35)));		
		g.setFont(fb);
		g.setColor(cb);
				
	}
	
	public void browseButtonActionPerformed() {
		int rv = fc.showOpenDialog(new JFrame(
		"Choose an image"));
		if (rv == JFileChooser.APPROVE_OPTION) {
			String file = fc.getSelectedFile().getPath();
			try {
				image = ImageIO.read(new File(
					file));
				imageOnLabel.setIcon(new ImageIcon(
					image));
				fileNameLabel.setText(fc
					.getSelectedFile().getName());
			} catch (Exception e) {
				e.printStackTrace();
				JOptionPane
					.showMessageDialog(
						null,
						file
							+ " is not a valid image file",
						"alert",
						JOptionPane.ERROR_MESSAGE);
			}
		}		
	}
	
	public static void drawThickLine(Cluster cluster,double dpi,Graphics g,Color c) {
		/*
		g.setColor(Color.RED);
		g.fillRect(cluster.getXmin(),cluster.getYmin(),cluster.getXmax()-cluster.getXmin(),cluster.getYmax()-cluster.getYmin());
		*/
		int linethickness = 3;
		drawThickLine(g,cluster.getXmin()*dpi,cluster.getYmin()*dpi,cluster.getXmax()*dpi,cluster.getYmax()*dpi,linethickness,c);
		drawThickLine(g,cluster.getXmax()*dpi,cluster.getYmin()*dpi,cluster.getXmin()*dpi,cluster.getYmax()*dpi,linethickness,c);
				
	}
	//same as Graphics.drawLine, but the line can be thick
	public static void drawThickLine(Graphics g, double d, double e, double f, double h, int thickness, Color c) {
			  // The thick line is in fact a filled polygon
			  g.setColor(c);
			  double dX = f - d;
			  double dY = h - e;
			  // line length
			  double lineLength = Math.sqrt(dX * dX + dY * dY);

			  double scale = (thickness) / (2 * lineLength);

			  // The x and y increments from an endpoint needed to create a rectangle...
			  double ddx = -scale * dY;
			  double ddy = scale * dX;
			  ddx += (ddx > 0) ? 0.5 : -0.5;
			  ddy += (ddy > 0) ? 0.5 : -0.5;
			  int dx = (int)ddx;
			  int dy = (int)ddy;

			  // Now we can compute the corner points...
			  int xPoints[] = new int[4];
			  int yPoints[] = new int[4];

			  xPoints[0] = (int)(d + dx); yPoints[0] = (int)(e + dy);
			  xPoints[1] = (int)(d - dx); yPoints[1] = (int)(e - dy);
			  xPoints[2] = (int)(f - dx); yPoints[2] = (int)(h - dy);
			  xPoints[3] = (int)(f + dx); yPoints[3] = (int)(h + dy);

			  g.fillPolygon(xPoints, yPoints, 4);
	}

	public JButton getBrowseButton() {
		return browseButton;
	}

	public void removeBrowseButton() {
		try {
			browsePanel.remove(browseButton);
		} catch (Exception e) {
			
		}
	}
	
	public JLabel getFileNameLabel() {
		return fileNameLabel;
	}

	public double getDpi() {
		return dpi;
	}

	public void setDpi(double dpi) {
		this.dpi = dpi;
	}

	public double getZoom() {
		return zoom;
	}

	public void setZoom(double zoom) {
		this.zoom = zoom;
		AffineTransformOp op = new AffineTransformOp(AffineTransform.getScaleInstance(zoom,zoom),AffineTransformOp.TYPE_BILINEAR);
		
		displayedImage = op.filter(image,null);
		imageOnLabel.setIcon(new ImageIcon(displayedImage));		
	}
	
}
