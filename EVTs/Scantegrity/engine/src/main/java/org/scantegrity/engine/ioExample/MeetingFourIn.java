package org.scantegrity.engine.ioExample;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.TreeMap;

import javax.xml.parsers.SAXParser;

import org.scantegrity.common.Drow;
import org.scantegrity.common.MeetingReaderSax;
import org.scantegrity.common.Util;

public class MeetingFourIn {

	public static void write(String m3out,String m4in) throws Exception {
		MeetingReaderSax handler = new MeetingReaderSax();
        try {
            SAXParser saxParser = Util.newSAXParser();
            saxParser.parse( new File(m3out), handler);
        } catch (Throwable t) {
            t.printStackTrace();
        }
        
        while (!handler.isDoneParsing()) {
        	Thread.sleep(100);
        }
        
        TreeMap<Byte, TreeMap<Byte, TreeMap<Integer, Drow>>> drows = handler.getDrows();
		
		Drow.ChosenSide side=Drow.ChosenSide.NONE;
		

		
OutputStream fos = new BufferedOutputStream(new FileOutputStream(m4in));
fos.write("<xml>\n".getBytes());
fos.write("\t<database>\n".getBytes());		
		
		for (byte p:drows.keySet()) {
			TreeMap<Byte, TreeMap<Integer, Drow>> partition=drows.get(p);
fos.write(("\t\t<partition id=\""+p+"\">\n").getBytes());
fos.write("\t\t\t<decrypt>\n".getBytes());
			for (byte i:partition.keySet()) {
				TreeMap<Integer, Drow> instance=partition.get(i);
fos.write(("\t\t\t\t<instance id=\""+i+"\">\n").getBytes());
				for (int did:instance.keySet()) {
					if (Math.random()<0.5)
						side=Drow.ChosenSide.LEFT;
					else
						side=Drow.ChosenSide.RIGHT;
fos.write(("\t\t\t\t\t<row id=\""+did+"\" side=\""+side+"\"/>\n").getBytes());
				}
				fos.write("\t\t\t\t</instance>\n".getBytes());							
			}
fos.write("\t\t\t</decrypt>\n".getBytes());
fos.write(("\t\t</partition>\n").getBytes());			
		}
fos.write("\t</database>\n".getBytes());
fos.write("</xml>".getBytes());
fos.close();
	}
}
