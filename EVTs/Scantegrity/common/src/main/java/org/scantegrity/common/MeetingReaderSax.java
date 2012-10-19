package org.scantegrity.common;

import java.util.TreeMap;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

/**
 * Reads an xml file representing a meeting and puts everything in memory
 * @author stefan
 *
 */
public class MeetingReaderSax extends DefaultHandler {
	TreeMap<Integer,Prow> prows=new TreeMap<Integer, Prow>();
	TreeMap<Byte,TreeMap<Byte,TreeMap<Integer,Drow>>> drows=new TreeMap<Byte, TreeMap<Byte,TreeMap<Integer,Drow>>>();;
	TreeMap<Byte,TreeMap<Integer,Rrow>> rrows=new TreeMap<Byte, TreeMap<Integer,Rrow>>();;
	
	TreeMap<Byte,TreeMap<Integer,Drow>> dPartition=null;
	TreeMap<Integer,Drow> dTable=null;
	
	TreeMap<Integer,Rrow> rTable=null;
	
	
	TreeMap<String,BallotRow> ballotRows=new TreeMap<String, BallotRow>();
	
	private enum Table {print,decrypt,results};
	Table whichTable;
	private byte partitionId;
	private byte dNo;

	boolean doneParsing=false;
	
	public MeetingReaderSax() {

	}
	
	public void startElement(String namespaceURI,String lName,String qName,Attributes attrs) {
        String eName = lName; // element name
        if ("".equals(eName)) eName = qName; // namespaceAware = false
    	if (eName.compareTo("print")==0) {
			whichTable=Table.print;
			return;
		}
    	if (eName.compareTo("decrypt")==0) {
			whichTable=Table.decrypt;			
			return;
		}
    	if (eName.compareTo("results")==0) {
			whichTable=Table.results;
			rTable= new TreeMap<Integer, Rrow>();
			return;
		}
    	
		if (eName.compareTo("partition")==0) {
			for (int i = 0; i < attrs.getLength(); i++) {
                String aName = attrs.getLocalName(i); // Attr name 
                if ("".equals(aName)) aName = attrs.getQName(i);				
				if (aName.equals("id")) {
					partitionId = Byte.parseByte(attrs.getValue(i));
				}
			}
			dPartition=new TreeMap<Byte, TreeMap<Integer,Drow>>();			
		}
		if (eName.compareTo("instance")==0) {
			for (int i = 0; i < attrs.getLength(); i++) {
                String aName = attrs.getLocalName(i); // Attr name 
                if ("".equals(aName)) aName = attrs.getQName(i);				
				if (aName.equals("id")) {
					dNo = Byte.parseByte(attrs.getValue(i));
				}
			}
			dTable = new TreeMap<Integer, Drow>();
		}

		if (eName.compareTo("row")==0) {
			if (whichTable==Table.print) {
				try {
					Prow prow=new Prow(attrs);
					prows.put(prow.getId(),prow);
				} catch (Exception e) {
					e.printStackTrace();
				}
			} else
			if (whichTable==Table.decrypt) {
				try {
					Drow drow = new Drow(attrs);
					dTable.put(drow.getId(), drow);
				} catch (Exception e) {
					e.printStackTrace();
				}				
			} else
			if (whichTable==Table.results) {
				try {
					Rrow rrow=new Rrow(attrs);
					rTable.put(rrow.getId(),rrow);
				} catch (Exception e) {
					e.printStackTrace();
				}				
			}
		}
		if (eName.compareTo("ballot")==0) {
			if (whichTable==Table.print) {
				try {
					BallotRow ballotRow=new BallotRow(attrs);
					ballotRows.put(ballotRow.getBarcodeSerial(),ballotRow);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}

    }
	
	public void endElement(String namespaceURI,	String sName, String qName) {
    	if (qName.equals("instance"))
    		dPartition.put(dNo, dTable);
    	else
    	if (qName.equals("results"))
    		rrows.put(partitionId, rTable);
    	else
    	if (qName.equals("partition"))
    		drows.put(partitionId, dPartition);
    	if (qName.equals("xml"))
    		doneParsing=true;    	
    }    

	public TreeMap<Byte, TreeMap<Byte, TreeMap<Integer, Drow>>> getDrows() {
		return drows;
	}

	public TreeMap<Integer, Prow> getProws() {
		return prows;
	}

	public TreeMap<Byte,TreeMap<Integer, Rrow>> getRrows() {
		return rrows;
	}
	
	public TreeMap<String, BallotRow> getBallotRows() {
		return ballotRows;
	}

	public boolean isDoneParsing() {
		return doneParsing;
	}
	
	
}