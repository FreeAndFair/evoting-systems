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

package org.scantegrity.common;

import java.util.TreeMap;

import org.xml.sax.Attributes;
import org.xml.sax.helpers.DefaultHandler;

public class CodesReaderSax extends DefaultHandler {
	//ballot,question,code
	TreeMap<Integer,TreeMap<Byte,TreeMap<Byte,SymbolRow>>> rows=new TreeMap<Integer, TreeMap<Byte,TreeMap<Byte,SymbolRow>>>();
	TreeMap<Byte,TreeMap<Byte,SymbolRow>> questions=new TreeMap<Byte, TreeMap<Byte,SymbolRow>>();
	TreeMap<Byte,SymbolRow> symbols=new TreeMap<Byte, SymbolRow>();
	
	TreeMap<Integer,BallotRow> serials=new TreeMap<Integer, BallotRow>();
	
	boolean doneParsing=false;
	
	
	int pid=-1;
	byte questionId=-1;
	
	byte smid=0;
	
	public CodesReaderSax() {

	}
	
	public void startElement(String namespaceURI,String lName,String qName,Attributes attrs) {
        String eName = lName; // element name
        if ("".equals(eName)) eName = qName; // namespaceAware = false
    	if (eName.compareTo("ballot")==0) {
			for (int i = 0; i < attrs.getLength(); i++) {
                String aName = attrs.getLocalName(i); // Attr name 
                if ("".equals(aName)) aName = attrs.getQName(i);				
				if (aName.equals(BallotRow.pidAttr)) {
					pid = Integer.parseInt(attrs.getValue(i));		
				}
			}
			questions=new TreeMap<Byte, TreeMap<Byte,SymbolRow>>();
			
			try {
				BallotRow ballotRow=new BallotRow(attrs);
				serials.put(pid, ballotRow);
			} catch (Exception e) {
				e.printStackTrace();
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
			symbols=new TreeMap<Byte, SymbolRow>();
			return;
		}
    	if (eName.compareTo("symbol")==0) {
    		try {
				SymbolRow sm=new SymbolRow(attrs);
				if (sm.getId()==-1)
					sm.setId(smid++);
				symbols.put(sm.getId(), sm);
			} catch (Exception e) {
				e.printStackTrace();
			}
			return;
		}		
    }
	
	public void endElement(String namespaceURI,	String sName, String qName) {
    	if (qName.equals("question"))
    		questions.put(questionId, symbols);
    	else
    	if (qName.equals("ballot"))
    		rows.put(pid, questions);
    	else
    	if (qName.equals("xml"))
    		doneParsing=true;    	
    }    

	public boolean isDoneParsing() {
		return doneParsing;
	}

	public TreeMap<Integer, TreeMap<Byte, TreeMap<Byte, SymbolRow>>> getRows() {
		return rows;
	}

	public TreeMap<Integer, BallotRow> getSerials() {
		return serials;
	}
	
}
