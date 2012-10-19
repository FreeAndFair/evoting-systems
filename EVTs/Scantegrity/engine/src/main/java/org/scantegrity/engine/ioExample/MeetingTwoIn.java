package org.scantegrity.engine.ioExample;

import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.Collections;
import java.util.Vector;

public class MeetingTwoIn {

	//write meeting two in
	public static void write(double percentCheck,int noBallots,String outFile) throws Exception {
		OutputStream fos = new BufferedOutputStream(new FileOutputStream(outFile));
fos.write("<xml>\n".getBytes());
fos.write("\t<challenges>\n".getBytes());
fos.write("\t\t<print>\n".getBytes());
		int[] a=random(percentCheck,noBallots);
		for (int i=0;i<a.length;i++) {
fos.write(("\t\t\t<row id=\""+a[i]+"\"/>\n").getBytes());				
		}
fos.write("\t\t</print>\n".getBytes());
fos.write("\t</challenges>\n".getBytes());
fos.write("</xml>\n".getBytes());			
fos.close();
	}
	
	public static int[] random(double percentCheck, int noBallots) {
		Vector<Integer> b = new Vector<Integer>(noBallots);
		for (int i=0;i<noBallots;i++)
			b.add(i);
		Collections.shuffle(b);
		
		int[] ret = new int[(int)(percentCheck*noBallots)];
		for (int i=0;i<ret.length;i++)
			ret[i] = b.get(i);
		
		return ret;
	}	
}
