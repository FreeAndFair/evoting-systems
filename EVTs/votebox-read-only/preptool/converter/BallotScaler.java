package preptool.converter;

import java.awt.Image;
import java.awt.image.BufferedImage;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;
import java.util.zip.ZipOutputStream;

import javax.imageio.ImageIO;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

public class BallotScaler {
	
	protected static void copy(InputStream in, String name, ZipOutputStream out) throws Exception{
		out.putNextEntry(new ZipEntry(name));
		
		int i;
		while((i = in.read()) != -1)
			out.write(i);
	}

	protected static void scaleLayout(InputStream in, String name, ZipOutputStream out, double scaleX, double scaleY) throws Exception{
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		int i;
		
		while((i = in.read()) != -1) baos.write(i);
		
		String str = new String(baos.toByteArray());
		
		out.putNextEntry(new ZipEntry(name));
		
		i = 0;
		int oldI = i;
		
		String buf = "";
		
		while((i = str.indexOf("x=\"", i)) != -1){
			i+=3;
			buf+=str.substring(oldI, i);
			
			int j = str.indexOf("\"", i);
			double newX = Integer.parseInt(str.substring(i,j));
			
			System.out.print("X: "+newX+" -> ");
			newX *= scaleX;
			System.out.println(""+newX);
			
			buf += (""+(int)newX);
			
			oldI = j;
		}
		
		buf += str.substring(oldI);
		
		i = 0;
		oldI = i;
		str = buf;
		buf = "";
		
		while((i = str.indexOf("y=\"", i)) != -1){
			i+=3;
			buf+=str.substring(oldI, i);
			
			int j = str.indexOf("\"", i);
			double newY = Integer.parseInt(str.substring(i,j));

			System.out.print("Y: "+newY+" -> ");
			newY *= scaleY;
			System.out.println(newY);
			
			buf += (""+(int)newY);
			
			oldI = j;
		}
		
		buf += str.substring(oldI);
		
		out.write(buf.getBytes());
	}
	
	protected static void scaleImage(InputStream in, String name, ZipOutputStream out, double scaleX, double scaleY) throws Exception{
		BufferedImage img = ImageIO.read(in);
		Image scaled = img.getScaledInstance((int)(img.getWidth()*scaleX), (int)(img.getHeight()*scaleY), Image.SCALE_SMOOTH);
		
		BufferedImage bScaled = new BufferedImage(img.getWidth(), img.getHeight(), BufferedImage.TYPE_INT_ARGB);
		bScaled.getGraphics().drawImage(scaled, 0, 0,null);
		
		out.putNextEntry(new ZipEntry(name));
		ImageIO.write(bScaled, "PNG", out);
	}
	
	protected static void scaleBallot(File in, File out, double scaleX, double scaleY) throws Exception{
		ZipFile ballot = new ZipFile(in);
		ZipOutputStream scaledBallot = new ZipOutputStream(new FileOutputStream(out));
		
		Enumeration<? extends ZipEntry> entries = ballot.entries();
		
		while(entries.hasMoreElements()){
			ZipEntry entry = entries.nextElement();
			
			if(entry.getName().endsWith(".png")){
				scaleImage(ballot.getInputStream(entry), entry.getName(), scaledBallot, scaleX, scaleY);
				continue;
			}
			
			if(entry.getName().endsWith(".xml") && !entry.getName().endsWith("ballot.xml")){
				scaleLayout(ballot.getInputStream(entry), entry.getName(), scaledBallot, scaleX, scaleY);
				continue;
			}
			
			copy(ballot.getInputStream(entry), entry.getName(), scaledBallot);
		}
		
		scaledBallot.flush();
		scaledBallot.close();
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) throws Exception{
		if(args.length != 4){
			System.out.println("Usage: java preptool.converter.BallotScaler [ballot zip file] [destination file] [width] [height]");
			System.exit(-1);
		}
		
		File ballot = new File(args[0]);
		if(!ballot.exists()){
			System.out.println("Ballot file not found");
			System.exit(-1);
		}
		
		File outBallot = new File(args[1]);
		if(outBallot.exists()){
			System.out.println("Destination file already exists");
			System.exit(-1);
		}
		
		int width = Integer.parseInt(args[2]);
		int height = Integer.parseInt(args[3]);
		
		double scaleX = ((double)width)/1024.0;
		double scaleY = ((double)height)/768.0;
		
		System.out.println("Scaling <"+scaleX+", "+scaleY+">");
		
		scaleBallot(ballot, outBallot, scaleX, scaleY);
	}

}
