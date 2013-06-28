/*
 * $Id: CandidateListXMLReader.java,v 1.10 2004/05/14 14:42:03 hubbers Exp $
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
import java.util.*;

//SAX
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.Attributes;
import org.xml.sax.helpers.AttributesImpl;


/**
 * XMLReader implementation for the CandidateList class. This class is used to
 * generate SAX events from the CandidateList class.
 *
 * @version $Id: CandidateListXMLReader.java,v 1.10 2004/05/14 14:42:03 hubbers Exp $
 *
 * @author Engelbert Hubbers (hubbers@cs.kun.nl)
 */
public class CandidateListXMLReader extends AbstractObjectReader {

   /**
    * @see org.xml.sax.XMLReader#parse(InputSource)
    */
   /*@
     @ also
     @ assignable objectState;
     @*/
   public void parse(InputSource input) throws IOException, SAXException {
      parse(MenuPanel.getTheMenuPanel().getCandidateList());
   }

   /**
    * Starts parsing the CandidateList object.
    * @param candidates The object to parse
    * @throws SAXException In case of a problem during SAX event generation
    */
   /*@
     @ assignable objectState;
     @*/
   public void parse(CandidateList candidates) throws SAXException {
      if (handler == null) {
         throw new IllegalStateException("ContentHandler not set");
      }
        
      //Start the document
      handler.startDocument();
        
      //Generate SAX events for the CandidateList
      generateFor(candidates);
      
      //End the document
      handler.endDocument();        
   }

    
   /**
    * Generates SAX events for a CandidateList object.
    * @param candidates CandidateList object to use
    * @throws SAXException In case of a problem during SAX event generation
    */
   /*@
     @ assignable objectState;
     @*/
   protected void generateFor(CandidateList candidates) throws SAXException {
      String attName;
      int j,k;
      if (handler == null) {
         throw new IllegalStateException("ContentHandler not set");
      }
        
      AttributesImpl atts = new AttributesImpl(); 
      attName = "action";
      atts.addAttribute ("", "", "action", "CDATA", "replace");
      attName = "contenttype";
      atts.addAttribute ("", "", "contenttype", "CDATA", "kieslijst");
      handler.startElement("result",atts);

      handler.startElement("metadata");
      handler.startElement("requestreference");
      handler.endElement("requestreference");
      handler.startElement("responsereference");
      handler.endElement("responsereference");
      handler.startElement("creationtime");
      handler.endElement("creationtime");
      handler.startElement("kieskringcount");
      handler.endElement("kieskringcount");
      handler.startElement("districtcount");
      handler.endElement("districtcount");
      handler.startElement("kieslijstcount");
      handler.endElement("kieslijstcount");
      handler.startElement("positiecount");
      handler.endElement("positiecount");
      handler.endElement("metadata"); 

      atts = new AttributesImpl();
      attName = "stembureau";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingBureau());
      attName = "voorzitter";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingChairman());
      attName = "state";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingState());
      attName = "verkiezing";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingElection());
      attName = "periode";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingInterval());
      attName = "stemming_start";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingElectionTimestampStart());
      attName = "stemming_eind";
      atts.addAttribute ("", attName, attName, "CDATA", AuditLog.getVotingElectionTimestampEnd());
      attName = "kiesgerechtigden";
      atts.addAttribute ("", attName, attName, "CDATA", Integer.toString(AuditLog.getVotingNrOfRegisteredVoters()));
      attName = "kiesgerechtigden_gestemd";
      atts.addAttribute ("", attName, attName, "CDATA", Integer.toString(AuditLog.getImportVotesNrOfVotes()));
      attName = "kiesgerechtigden_niet_gestemd";
      atts.addAttribute ("", attName, attName, "CDATA", Integer.toString(AuditLog.getVotingNrOfRegisteredVoters()-AuditLog.getImportVotesNrOfVotes()));
      handler.startElement("globaal",atts);
      handler.endElement("globaal");
      Set orderedKiesKringen = candidates.my_kieskringen.keySet(); 
      assert (orderedKiesKringen != null);
      Iterator i = orderedKiesKringen.iterator();
      assert (i != null);   
      while (i.hasNext()) {
         Byte b = (Byte)(i.next());
         KiesKring kiesKring = (KiesKring)(candidates.my_kieskringen.get(b));
         atts = new AttributesImpl();
         attName = "nummer";
         atts.addAttribute ("", attName, attName, "CDATA",Byte.toString(kiesKring.number()));
         attName = "naam";
         atts.addAttribute ("",attName, attName,  "CDATA",kiesKring.name());
         handler.startElement("kieskring",atts);

         for (j=0; j<kiesKring.getDistricten().length; j++) {
            District district = kiesKring.getDistricten()[j];
            if (district != null) {
               atts = new AttributesImpl();
               attName = "nummer";
               atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(district.number()));
               attName = "naam";
               atts.addAttribute ("", attName, attName, "CDATA",district.name());
               handler.startElement("district",atts);
               handler.endElement("district");
            }
         }
         for (j = 0; j < kiesKring.getKiesLijsten().length; j++) {
            KiesLijst kiesLijst = kiesKring.getKiesLijsten()[j];     
            if (kiesLijst != null) {
               atts = new AttributesImpl();
               attName = "nummer";
               atts.addAttribute ("", attName, attName, "CDATA",Short.toString(kiesLijst.number()));
               attName = "groepering";
               atts.addAttribute ("", attName, attName, "CDATA",kiesLijst.name());
               attName = "stemmen";
               atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(kiesLijst.voteCount()));
               handler.startElement("kieslijst",atts);
               for (k = 0; k < kiesLijst.my_candidates.length; k++) {
                  Candidate candidate = kiesLijst.my_candidates[k];
                  if (candidate != null) {
                     atts = new AttributesImpl();
                     attName = "nummer";
                     atts.addAttribute ("", attName, attName, "CDATA",Byte.toString(candidate.position_number()));
                     attName = "achternaam";
                     atts.addAttribute ("", attName, attName, "CDATA",candidate.lastname());
                     attName = "voorletters";
                     atts.addAttribute ("", attName, attName, "CDATA",candidate.initials());
                     attName = "roepnaam";
                     atts.addAttribute ("", attName, attName, "CDATA",candidate.firstname());
                     attName = "geslacht";
                     atts.addAttribute ("", attName, attName, "CDATA",Character.toString(candidate.gender()));
                     attName = "woonplaats";
                     atts.addAttribute ("", attName, attName, "CDATA",candidate.cityOfResidence());
                     attName = "stemmen";
                     atts.addAttribute ("", attName, attName, "CDATA",Integer.toString(candidate.voteCount()));
                     handler.startElement("positie",atts);
                     handler.endElement("positie");
                  }
               }
               handler.endElement("kieslijst");
            }
         }
      }
      handler.endElement("kieskring");
      handler.endElement("result");
   }
}
