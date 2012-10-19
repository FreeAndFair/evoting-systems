package org.scantegrity.common.auditing;

import java.util.TreeMap;

import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

import org.scantegrity.common.BallotRow;
import org.scantegrity.common.SecurityUtil;
import org.scantegrity.common.SymbolRow;

public class ParseM2CodesCheckCommitments extends DefaultHandler {

	int pid=-1;
	byte questionId=-1;
	TreeMap<Integer,TreeMap<Byte,TreeMap<Byte,SymbolRow>>> rows=null;
	
	TreeMap<Integer,BallotRow> serials=null;
	
	byte[] c=null;
	
	public ParseM2CodesCheckCommitments(TreeMap<Integer,TreeMap<Byte,TreeMap<Byte,SymbolRow>>> rows, TreeMap<Integer,BallotRow> serials, byte[] c) {
		this.rows=rows;
		this.serials=serials;
		this.c=c;
	}
	
	public void startElement(String namespaceURI,String lName,String qName,Attributes attrs) throws SAXException {
        String eName = lName; // element name
        if ("".equals(eName)) eName = qName; // namespaceAware = false
    	if (eName.compareTo("ballot")==0) {
    		
    		BallotRow ballotRowToBeCHecked=null;
			try {
				ballotRowToBeCHecked = new BallotRow(attrs);
			} catch (Exception e) {
				e.printStackTrace();
			}
    		pid=ballotRowToBeCHecked.getPid();
    		
    		BallotRow ballotRowCommitment=serials.get(pid);
    		if (ballotRowCommitment!=null) {    		
				SecurityUtil.checkSerialsCommitment(ballotRowToBeCHecked, ballotRowCommitment, c);
    		}
			return;
		}
    	if (eName.compareTo("question")==0) {
			for (int i = 0; i < attrs.getLength(); i++) {
                String aName = attrs.getLocalName(i); // Attr name 
                if ("".equals(aName)) aName = attrs.getQName(i);				
				if (aName.equals("id")) {
					questionId = Byte.parseByte(attrs.getValue(i));;		
				}
			}
			return;
		}
    	if (eName.compareTo("symbol")==0) {
				SymbolRow symbolCommitment=null;
				try {
					symbolCommitment = new SymbolRow(attrs);
				} catch (Exception e) {
					e.printStackTrace();
				}
				TreeMap<Byte,TreeMap<Byte,SymbolRow>> ballot=rows.get(pid);
				if (ballot!=null) {
					TreeMap<Byte,SymbolRow> question=ballot.get(questionId);
					if (question!=null) {						
						SymbolRow symbolSalt=question.get(symbolCommitment.getId()); 
						if (symbolSalt!=null) {	
							
							SecurityUtil.checkCodeCommitment(pid, questionId, symbolCommitment.getId(), symbolSalt.getSalt(), symbolSalt.getCode(), symbolCommitment.getCommitment(), c);
						}
					}
				}								
				return;
    	}
	}
}
