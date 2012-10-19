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

import java.io.Serializable;

import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.xml.sax.Attributes;

import com.itextpdf.text.pdf.codec.Base64;

public class SymbolRow implements Serializable {

	private static final long serialVersionUID = 1L;
	
	public static final String idAttr="id";
	public static final String codeAttr="code";
	public static final String saltAttr="salt";
	public static final String commitmentAttr="c";
	
	byte id=-1;
	String code=null;
	byte[] commitment=null;
	byte[] salt=null;
	
	public SymbolRow() {
		
	}
	
	public SymbolRow(Node node) throws Exception {
		setUp(node);
	}
	
	public SymbolRow(Attributes attrs) throws Exception {
		setUp(attrs);
	}

	
	protected void setUp(Node row) throws Exception {
		NamedNodeMap attrs = row.getAttributes();
		Node attr=null;
		
		attr=attrs.getNamedItem(idAttr);
		if (attr!=null)
			id=Byte.parseByte(attr.getNodeValue());

		attr=attrs.getNamedItem(codeAttr);
		if (attr!=null)
			code=attr.getNodeValue();
		
		attr=attrs.getNamedItem(commitmentAttr);
		if (attr!=null)
			commitment=Base64.decode(attr.getNodeValue());
		
		attr=attrs.getNamedItem(saltAttr);
		if (attr!=null)
			salt=Base64.decode(attr.getNodeValue());
	}

	protected void setUp(Attributes attrs) throws Exception {
		for (int i = 0; i < attrs.getLength(); i++) {
            String aName = attrs.getLocalName(i);
            if ("".equals(aName)) aName = attrs.getQName(i);
			if (aName.equals(idAttr))
				id = Byte.parseByte(attrs.getValue(i));
			else
			if (aName.equals(codeAttr))
				code=attrs.getValue(i);
			else
			if (aName.equals(saltAttr))
				salt = Base64.decode(attrs.getValue(i));
			else
			if (aName.equals(commitmentAttr))
				commitment = Base64.decode(attrs.getValue(i));
		}		
	}
	
	public String getCode() {
		return code;
	}
	public void setCode(String code) {
		this.code = code;
	}
	public byte[] getCommitment() {
		return commitment;
	}
	public void setCommitment(byte[] commitment) {
		this.commitment = commitment;
	}
	public byte getId() {
		return id;
	}
	public void setId(byte id) {
		this.id = id;
	}
	public byte[] getSalt() {
		return salt;
	}
	public void setSalt(byte[] salt) {
		this.salt = salt;
	}
	
	public String toString() {
		StringBuffer ret=new StringBuffer("");

		ret.append("\t\t\t<symbol id=\""+getId()+"\"");
		if (salt!=null) {
			ret.append(" "+saltAttr+"=\""+new String(Base64.encodeObject(salt))+"\"");
		}
		if (code!=null) {
			ret.append(" "+codeAttr+"=\""+code+"\"");
		}
		if (commitment!=null) {
			ret.append(" "+commitmentAttr+"=\""+new String(Base64.encodeObject(commitment))+"\"");
		}
		ret.append("/>\n");
		return ret.toString();
	}
}
