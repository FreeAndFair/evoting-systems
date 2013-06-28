/*
 * $Id: AuditLogXMLReader.java,v 1.9 2004/05/18 12:44:54 hubbers Exp $
 * ============================================================================
 *                    The Apache Software License, Version 1.1
 * ============================================================================
 * 
 * Copyright (C) 1999-2003 The Apache Software Foundation. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modifica-
 * tion, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 
 * 3. The end-user documentation included with the redistribution, if any, must
 *    include the following acknowledgment: "This product includes software
 *    developed by the Apache Software Foundation (http://www.apache.org/)."
 *    Alternately, this acknowledgment may appear in the software itself, if
 *    and wherever such third-party acknowledgments normally appear.
 * 
 * 4. The names "FOP" and "Apache Software Foundation" must not be used to
 *    endorse or promote products derived from this software without prior
 *    written permission. For written permission, please contact
 *    apache@apache.org.
 * 
 * 5. Products derived from this software may not be called "Apache", nor may
 *    "Apache" appear in their name, without prior written permission of the
 *    Apache Software Foundation.
 * 
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND ANY EXPRESSED OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * APACHE SOFTWARE FOUNDATION OR ITS CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLU-
 * DING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS
 * OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ============================================================================
 * 
 * This software consists of voluntary contributions made by many individuals
 * on behalf of the Apache Software Foundation and was originally created by
 * James Tauber <jtauber@jtauber.com>. For more information on the Apache
 * Software Foundation, please see <http://www.apache.org/>.
 */ 
package sos.koa;

//Java
import java.util.Iterator;
import java.io.IOException;

//SAX
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.Attributes;
import org.xml.sax.helpers.AttributesImpl;


/**
 * XMLReader implementation for the AuditLog class. This class is used to
 * generate SAX events from the AuditLog class.
 *
 * @version $Id: AuditLogXMLReader.java,v 1.9 2004/05/18 12:44:54 hubbers Exp $
 *
 * @author Engelbert Hubbers (hubbers@cs.kun.nl)
 */
public class AuditLogXMLReader extends AbstractObjectReader {

    /**
     * @see org.xml.sax.XMLReader#parse(InputSource)
     */
 
    /*@
      @ also
      @ assignable objectState;
      @*/
    public void parse(InputSource input) throws IOException, SAXException, IllegalStateException {
       parse();
    }


    /**
     * Starts parsing the AuditLog object.
     *
     * @exception SAXException in case of a problem during SAX event generation.
     */
    /*@
      @ assignable objectState;
      @*/
    public void parse() throws SAXException, IllegalStateException {
        if (handler == null) {
            throw new IllegalStateException("ContentHandler not set");
        }
        //@ assert handler != null; 
        //Start the document
        handler.startDocument();
        //@ assert handler != null; 
        
        //Generate SAX events for the AuditLog
        generateFor();
        //@ assert handler != null; 
        
        //End the document
        handler.endDocument();        
    }

    
    /**
     * Generates SAX events for a AuditLog object.
     *
     * @exception SAXException In case of a problem during SAX event generation.
     */
    /*@
      @ assignable objectState;
      @ ensures handler != null;
      @*/
    protected void generateFor() throws SAXException, IllegalStateException {
        String attName;
        if (handler == null) {
            throw new IllegalStateException("ContentHandler not set");
        }
        
        AttributesImpl atts = new AttributesImpl(); 
        attName = "timestamp";
        atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getLogTimestamp());
        handler.startElement("log",atts);

        // importcandidates
        atts = new AttributesImpl(); 
        attName = "success";
        if (AuditLog.getImportCandidatesSuccess()) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");
          handler.startElement("importcandidates",atts);

        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
          handler.startElement("importcandidates",atts);
          handler.element("error",AuditLog.getImportCandidatesError());
        }
        atts = new AttributesImpl(); 
        attName = "location";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportCandidatesFileName());
        attName = "timestamp";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportCandidatesFileTimestamp());
        handler.startElement("file",atts);
        handler.endElement("file");

        atts = new AttributesImpl(); 
        attName = "refnr";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportCandidatesRefNr());
        attName = "nroflists";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getImportCandidatesNrOfLists()));
        attName = "nrofcandidates";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getImportCandidatesNrOfCandidates()));
        attName = "nrofblanco";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getImportCandidatesNrOfBlanco()));
        handler.startElement("candidatecontents",atts);
        handler.endElement("candidatecontents");
        handler.endElement("importcandidates");
        
        // importvotes
        atts = new AttributesImpl(); 
        attName = "success";
        if (AuditLog.getImportVotesSuccess()) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");
          handler.startElement("importvotes",atts);

        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
          handler.startElement("importvotes",atts);
          handler.element("error",AuditLog.getImportVotesError());
        }
        atts = new AttributesImpl(); 
        attName = "location";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportVotesFileName());
        attName = "timestamp";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportVotesFileTimestamp());
        handler.startElement("file",atts);
        handler.endElement("file");

        atts = new AttributesImpl(); 
        attName = "nrofkieskringen";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getImportVotesNrOfKieskringen()));
        attName = "nrofvotes";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getImportVotesNrOfVotes()));
        handler.startElement("votecontents",atts);
        handler.endElement("votecontents");
        handler.endElement("importvotes");
        
        // importprivkey
        atts = new AttributesImpl(); 
        attName = "success";
        if (AuditLog.getImportPrivKeySuccess()) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");
          handler.startElement("importprivkey",atts);

        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
          handler.startElement("importprivkey",atts);
          handler.element("error",AuditLog.getImportPrivKeyError());
        }
        atts = new AttributesImpl(); 
        attName = "location";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportPrivKeyFileName());
        attName = "timestamp";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportPrivKeyFileTimestamp());
        handler.startElement("file",atts);
        handler.endElement("file");
        handler.endElement("importprivkey");
        
        // importpubkey
        atts = new AttributesImpl(); 
        attName = "success";
        if (AuditLog.getImportPubKeySuccess()) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");
          handler.startElement("importpubkey",atts);

        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
          handler.startElement("importpubkey",atts);
          handler.element("error",AuditLog.getImportPubKeyError());
        }
        atts = new AttributesImpl(); 
        attName = "location";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportPubKeyFileName());
        attName = "timestamp";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getImportPubKeyFileTimestamp());
        handler.startElement("file",atts);
        handler.endElement("file");
        handler.endElement("importpubkey");
        
        // keypair
        atts = new AttributesImpl(); 
        attName = "success";
        if (AuditLog.getKeypairSuccess()) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");
          handler.startElement("keypair",atts);

        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
          handler.startElement("keypair",atts);
        }
        handler.endElement("keypair");
        
        // decrypt
        atts = new AttributesImpl(); 
        attName = "success";
        Object[] decryptErrors = AuditLog.getDecryptErrors();
        if (AuditLog.getDecryptSuccess() && decryptErrors.length == 0) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");

        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
        }
        handler.startElement("decrypt",atts);
        for (int i = 0; i < decryptErrors.length; i++) {
           handler.element("error",(String)decryptErrors[i]);
        }
        atts = new AttributesImpl(); 
        attName = "start";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getDecryptTimestampStart());
        attName = "end";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getDecryptTimestampEnd());
        handler.startElement("runtime",atts);
        handler.endElement("runtime");

        atts = new AttributesImpl(); 
        attName = "nrofvotes";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getDecryptNrOfVotes()));
        handler.startElement("result",atts);
        handler.endElement("result");
        handler.endElement("decrypt");
        
        // count
        atts = new AttributesImpl(); 
        attName = "success";
        Object[] countErrors = AuditLog.getCountErrors();
        if (AuditLog.getCountSuccess() && countErrors.length == 0) {
          atts.addAttribute ("", attName, attName, "CDATA", "yes");
        } else {
          atts.addAttribute ("", attName, attName, "CDATA", "no");
        }
        handler.startElement("count",atts);
        for (int i = 0; i < countErrors.length; i++) {
           handler.element("error",(String)countErrors[i]);
        }
        atts = new AttributesImpl(); 
        attName = "start";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getCountTimestampStart());
        attName = "end";
        atts.addAttribute ("", attName, attName, "CDATA",AuditLog.getCountTimestampEnd());
        handler.startElement("runtime",atts);
        handler.endElement("runtime");

        atts = new AttributesImpl(); 
        attName = "nrofvotes";
        atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(AuditLog.getCountNrOfVotes()));
        handler.startElement("result",atts);
        handler.endElement("result");
        handler.endElement("count");
        
        handler.endElement("log");
    }
}
