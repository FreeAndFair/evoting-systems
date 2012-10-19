package org.scantegrity.engine.ioExample;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;

import org.bouncycastle.util.encoders.Base64;

public class MeetingOneIn {

	public static void write(String es,int noB,int noD,byte[] c,String partitions,String outFile) throws IOException {
				
		//File f=new File(outFile);
		//if (!f.exists())
			//f.createNewFile();
			
		//write meeting one in
		OutputStream fos = new BufferedOutputStream(new FileOutputStream(outFile));
		fos.write("<xml>\n".getBytes());
			fos.write("\t<electionSpec>".getBytes());
			fos.write(es.getBytes());
			fos.write("</electionSpec>\n".getBytes());
		
			fos.write(("\t<noBallots>"+noB+"</noBallots>\n").getBytes());
			
			fos.write(("\t<noDs>"+noD+"</noDs>\n").getBytes());
		
			fos.write("\t<constant>".getBytes());
			fos.write(Base64.encode(c));
			fos.write("</constant>\n".getBytes());

			fos.write("\t<partitions>".getBytes());
			fos.write(partitions.getBytes());
			fos.write("</partitions>\n".getBytes());

			
		fos.write("</xml>\n".getBytes());		
		fos.close();
	}	
}
