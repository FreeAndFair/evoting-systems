package action;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.apache.struts.action.Action;
import org.apache.struts.action.ActionForm;
import org.apache.struts.action.ActionForward;
import org.apache.struts.action.ActionMapping;

import propmgr.PropertyLoader;
import util.*;
import forms.CountingForm;
import valueobject.BallotVO;



public class CountingAction extends Action
{
	StringBuffer logSB = new StringBuffer();
	 PropertyLoader pl;
	 Properties prop;
	 public String xmlString;
	 public HashMap ballotLookupXMLMap;
	 public HashMap countingLookupXMLMap;
	 public HashMap countingXMLMap;
 public CountingAction()
 {
     xmlString = null;
     ballotLookupXMLMap = new HashMap();
     countingLookupXMLMap = new HashMap();
     countingXMLMap = new HashMap();
     
 }

 public ActionForward execute(ActionMapping actionmapping, ActionForm actionform, HttpServletRequest httpservletrequest, HttpServletResponse httpservletresponse)
     throws Exception
 {
     String forwardName = "defaultPage";
     try {
			
    	 	//pl = new PropertyLoader("http://localhost:8080/connecticutVotingDemo/properties/application.properties");
			pl = new PropertyLoader("http://openvotingsolutions.info/connecticutVotingDemo/properties/application.properties");
			prop = pl.getCache();
		} catch (Exception e) {
			e.printStackTrace();
		}

     try
     {
         CountingForm countingform = (CountingForm)actionform;
         HashMap hashmap = new HashMap();
         BallotVO ballotvo = new BallotVO();
         MessageBean messagebean = new MessageBean();
         httpservletrequest.setAttribute("messageBean", messagebean);
         makeWarning(httpservletrequest, "Welcome to Counting! Please click on the given below enabled button to process the counting...! ");
         String countingType = countingform.getCountingType();
         logSB.append("CountingType "+countingType+"\r\n");
         if(countingType.equals("ballotToEML440")) {
        	 System.out.print("ballotToEML440");			
		    String ballotLookupFolder = prop.getProperty("ballotLookupFolder");
		    System.out.println("ballotLookupFolder "+ballotLookupFolder);
			//parse and map ballot look up
			parseBallotLookup(ballotLookupFolder);
			
			try {
				// Ballot XML Parser				
				HashMap listOfBallotMap = new HashMap();
				String ballotFolder = prop.getProperty("ballotFolder");
				// Reading list of BALLOT XML file
				listOfBallotMap = readListofFiles(ballotFolder);
				if (listOfBallotMap != null) {
					System.out.println("listOfEMLXMLs "	+ listOfBallotMap.size());
					Set keySet = listOfBallotMap.keySet();
					if (keySet != null) {
						Iterator bIt = keySet.iterator();
						while (bIt.hasNext()) {
							String key = (String) bIt.next();
							xmlString = (String) listOfBallotMap.get(key);
							System.out.println("Ballot XML size "+ xmlString.toString());
							BallotXMLMap ballotMap = new BallotXMLMap();
							HashMap ballotXMLMap = ballotMap.getXMLMap(xmlString.toString().trim());
							System.out.println("\r\n\r\nballotXMLMap Size "+ballotXMLMap.size()
									+" ballotLookupXMLMap "+ballotLookupXMLMap.size());
							logSB.append("\r\n\r\nballotXMLMap Size "+ballotXMLMap.size()
									+" ballotLookupXMLMap "+ballotLookupXMLMap.size());
							writeFile(logSB.toString());
							//ballotVO.setBallotData(ballotXMLMap);
							xmlString = null;
							// Generate EML440 XML file						
							generateEML440(ballotXMLMap, ballotLookupXMLMap);							
							ballotXMLMap=new HashMap();
							//System.out.println("\r\n\r\nballotXMLMap Size "+ballotXMLMap.size());
							
						}
					}
				}
				ballotvo.setTransactionDetails("Ballot to EML440 has been converted successfully...!");
				countingform.setCountingType("eml440To510");
			} catch (Exception e) {				
				System.out.println("Exception in Ballot..." + e.getMessage());
				ballotvo.setTransactionDetails(e.toString());
				
			}
		} 

         if(countingType.equals("eml440To510"))
         {
             System.out.print("eml440To510");
             logSB.append("inside the eml440To510 if condition\r\n");
             countingform.setCountingType("eml510To520");
             HashMap emlXMLMap = new HashMap();
             emlXMLMap = getEMLXMLCountingDataMap();
             System.out.println("emlXMLMap "+emlXMLMap.size());
             generateEML510(emlXMLMap);
             logSB.append("EML440 to EML510 has been converted successfully...!");
             writeFile(logSB.toString());
             ballotvo.setTransactionDetails("EML440 to EML510 has been converted successfully...!");
         }
         if(countingType.equals("eml510To520"))
         {
             System.out.print("eml510To520");
             countingform.setCountingType("done");
             forwardName = "success";
             parseCounting410Lookup();
             parse510XML();
             generateEML520();
             makeWarning(httpservletrequest, "");
         }
         if(httpservletrequest.getParameter("countingType") != null && httpservletrequest.getParameter("countingType").equals("done"))
         {
             makeWarning(httpservletrequest, "");
             System.out.print("Inside done...!!!");
             countingform.setCountingType("done");
         }
         System.out.println("countingType " + countingType);
         System.out.println("Forward Status " + forwardName);
         writeFile(logSB.toString());
     }
     catch(Exception exception1)
     {
         exception1.printStackTrace();
         writeFile(logSB.toString());
     }
     return actionmapping.findForward(forwardName);
 }

 public void writeFile(String XMLData)
 {   
     try
     {  
    	 //FileOutputStream fileoutputstream = new FileOutputStream("counting-ovs.log");
    	 FileOutputStream fileoutputstream = new FileOutputStream("/home/ovsadmin/public_html/connecticutVotingDemo/ovs-counting.log");
         
         for(int i = 0; i < XMLData.length(); i++)
             fileoutputstream.write(XMLData.charAt(i));

         fileoutputstream.close();
     }
     catch(Exception exception)
     {
         exception.printStackTrace();
     }
 }


 public void generateEML520()
 {
	 
     StringBuffer resultXML = new StringBuffer();
	 resultXML.append("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n");
	 resultXML.append("<?xml-stylesheet type=\"text/xsl\" href=\"http://openvotingsolutions.info/connecticutVotingDemo/xml/eml520result/ovs-EML520-results.xsl\"?>\r\n");
	 resultXML.append("<EML xmlns:ovs=\"http://www.openvotingsolutions.com\" Id=\"520\" SchemaVersion=\"4.0\">\r\n");
	 resultXML.append("<TransactionId>2007-04-18</TransactionId>\r\n");
	 resultXML.append("<Result>\r\n");
	 resultXML.append("<Election>\r\n");
	 resultXML.append("<EventIdentifier Id=\"State of Connecticut Election -2007, \" />\r\n");
 	 String candidateID="",partyKey="",candidateName="",displayKey="";
 	 int displayOrder=0;
	 for(int i=1;i<=11;i++) {
		 resultXML.append("<Contest>\r\n");
		 resultXML.append("<ContestIdentifier Id=\""+countingLookupXMLMap.get("fID"+i)+"\" />\r\n");
	    for(int j=1;j<=7;j++) {
	    	partyKey="fID" + i + "pID" + j;
	    	displayKey="dID" + i + "pID" + j;
	    	candidateName="cID" + i + "pID" + j;
	    	candidateID= (String) countingLookupXMLMap.get(partyKey);
	    	displayOrder++;
	    	resultXML.append("<Selection>\r\n");
	    	resultXML.append("<CandidateIdentifier ID=\""+candidateID+"\" DisplayOrder=\""+displayOrder+"\">\r\n");
	    	resultXML.append("<CandidateName>"+countingLookupXMLMap.get(candidateName)+"</CandidateName>\r\n");
	    	resultXML.append("</CandidateIdentifier>\r\n");
	    	resultXML.append("<Affiliation>\r\n");
	    	resultXML.append("<AffiliationIdentifier ID=\"DEM\">\r\n");
	    	resultXML.append("<RegisteredName>"+countingLookupXMLMap.get(candidateID)+"</RegisteredName>\r\n");
	    	resultXML.append("</AffiliationIdentifier>\r\n");
	    	resultXML.append("</Affiliation>\r\n");
	    	resultXML.append("<Votes>"+countingXMLMap.get(candidateID)+"</Votes>\r\n");
	    	resultXML.append("</Selection>\r\n");
	    }
	    resultXML.append("</Contest>\r\n");
	
	}
	 resultXML.append("</Election>\r\n");
	 resultXML.append("</Result>\r\n");
	 resultXML.append("</EML>\r\n");
     String resultFolder = prop.getProperty("eml520ResultFolder");
     writeFile(resultFolder, resultXML.toString());
 }

 public void parse510XML()
 {
     Counting510XMLMap counting510xmlmap = new Counting510XMLMap();
     try
     {
         String s = prop.getProperty("eml510CountingFolder");
         xmlString = ReadFile(s);
         System.out.println("Counting410Lookup\r\n" + xmlString);
         countingXMLMap = counting510xmlmap.getXMLMap(xmlString.toString().trim());
         System.out.println("countingXMLMap size \r\n" + countingXMLMap.size());
         xmlString = null;
     }
     catch(Exception exception)
     {
         System.out.println("Exception in countingXMLMap... " + exception.getMessage());
         exception.printStackTrace();
     }
 }

 public void parseCounting410Lookup()
 {
     Counting410Lookup counting410lookup = new Counting410Lookup();
     try
     {
         String s = prop.getProperty("eml410LookupFolder");
         xmlString = ReadFile(s);
         countingLookupXMLMap = counting410lookup.getXMLMap(xmlString.toString().trim());
         System.out.println("countingLookupXMLMap size \r\n" + countingLookupXMLMap.size());
         xmlString = null;
     }
     catch(Exception exception)
     {
         System.out.println("Exception in Counting410Lookup... " + exception.getMessage());
         exception.printStackTrace();
     }
 }

 public void generateEML510(HashMap emlXMLMap) {
			
		StringBuffer xmlString = new StringBuffer();
		xmlString.append("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n");
		xmlString.append(" <EML Id=\"510\" schemaVersion=\"4.0\">\r\n");	
		xmlString.append("<EventIdentifier Id=\"State Of Connecticut - USA\" />\r\n");
		xmlString.append("<Election>\r\n");
		xmlString.append("<ElectionIdentifier Id=\"State Election\" />\r\n");
	
		String candidateID="",partyKey="",wKey="",candidateKey="";
		for(int i=1;i<=11;i++) {
			xmlString.append("<Contest>\r\n");
			xmlString.append("<ContestIdentifier Id=\""+i+"\" />\r\n");
			xmlString.append("<TotalVotes>\r\n");
		    for(int j=1;j<=7;j++) {
		    	partyKey="fID" + i + "pID" + j;	
		    	wKey = "cID"+i+"wID"+j;
		    	candidateKey="cID" + i + "pID" + j;
		    	xmlString.append("<Selection ID=\""+j+"\">\r\n");
		    	xmlString.append("<CandidateIdentifier ID=\""+emlXMLMap.get(candidateKey)+"\"/>\r\n");
		    	xmlString.append("<WriteinCandidateName />\r\n");
		    	xmlString.append("<ValidVotes>"+emlXMLMap.get(partyKey)+"</ValidVotes>\r\n");		    	
		    	xmlString.append("</Selection>\r\n");
		    }
		    xmlString.append("</TotalVotes>\r\n");
		    xmlString.append("</Contest>\r\n");
		}
		xmlString.append("</Election>\r\n");
		xmlString.append("</EML>\r\n");
		
		String eml510CountingFolder = prop.getProperty("eml510CountingFolder");	
		//String fileName="emlcounting/EML510_Counting.xml";
		
		writeFile(eml510CountingFolder,xmlString.toString());		

	}
  public HashMap getEMLXMLCountingDataMap() {
		HashMap listOfEMLXMLs = new HashMap();
		HashMap emlXMLMap = new HashMap();
		int oldVal = 0, newVal = 0, setVal = 0;
		String xmlString = null;
		String oldValS;
		String newValS;
		String eml440Folder = prop.getProperty("eml440Folder");
		String partyKey=null;
		HashMap votedKeysMap = new HashMap();
		 for(int i=1;i<=11;i++) {
			 for(int j=1;j<=7;j++) {
				 partyKey="fID" + i + "pID" + j; 
				 votedKeysMap.put(partyKey, partyKey);
			 }
		 }
		
		listOfEMLXMLs = readListofFiles(eml440Folder);
		if (listOfEMLXMLs != null) {
			System.out.println("listOfEMLXMLs " + listOfEMLXMLs.size());
			Set keySet = listOfEMLXMLs.keySet();
			if (keySet != null) {
				Iterator bIt = keySet.iterator();
				while (bIt.hasNext()) {
					String key = (String) bIt.next();
					xmlString = (String) listOfEMLXMLs.get(key);
					// EML Parser
					if (xmlString != null) {
						EMLXMLMap emlMap = new EMLXMLMap();
						HashMap mapNew = new HashMap();
						mapNew = emlMap.getXMLMap(xmlString);
						Set oldKeySet = emlXMLMap.keySet();
						if (mapNew != null) {
							Set newkeySet = mapNew.keySet();
							if (newkeySet != null) {
								Iterator newIt = newkeySet.iterator();
								while (newIt.hasNext()) {
									Object newKeyObj = newIt.next();
									String newkey = (String) newKeyObj;
									System.out.println("new key " + newkey);
									if (oldKeySet.contains(newKeyObj)) {
										if(votedKeysMap.get(newkey)!=null){
												 oldValS=emlXMLMap.get(newkey).toString();
												 newValS=mapNew.get(newkey).toString();
												 System.out.println("oldVal "+oldValS+" "+oldValS.length());
												 System.out.println("newVal "+newValS+" "+newValS.length());
												 oldVal = Integer.parseInt(oldValS);
												 newVal = Integer.parseInt(newValS);
												 setVal = oldVal + newVal;
												 System.out.println("Set Val " + setVal);
												 emlXMLMap.put(newkey, new Integer(setVal));
										}							
									} else {
										System.out.println("Else of the key "+newkey +" -> "+mapNew.get(newkey));
										emlXMLMap.put(newkey, mapNew.get(newkey));
									}
								}
							}
						}
					}
				}
			}
		}
		return emlXMLMap;
	}

 
 public HashMap readListofFiles(String s)
 {
     HashMap hashmap = new HashMap();
     Object obj = null;
     File file = new File(s);
     File afile[] = file.listFiles();
     Object obj1 = null;
     if(afile != null)
     {
         System.out.println(" ROOT FILES SIZE " + afile.length);
         for(int i = 0; i < afile.length; i++)
         {
             if(afile[i].isDirectory())
                 continue;
             try
             {
                 String s2 = afile[i].getName();
                 if(s2.toUpperCase().endsWith(".XML"))
                 {
                     System.out.println("readListofFiles - Reading->" + s2);
                     String s1 = ReadFile(s + File.separator + s2);
                     hashmap.put(s2, s1);
                     s1 = null;
                 }
             }
             catch(Exception exception)
             {
                 System.out.println("readListofFiles -> " + exception.toString());
             }
         }

     }
     System.out.println("Map Size " + hashmap.size());
     return hashmap;
 }

 public void generateEML440(HashMap ballotXMLMap, HashMap ballotLookupXMLMap) {
		
		String transactionID = (String) ballotXMLMap.get("ballotTransactionID");
		System.out.print("transactionID "+transactionID);
		StringBuffer emlXML = new StringBuffer();
		emlXML.append("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n");
		emlXML.append("<EML xmlns:ovs=\"http://www.openvotingsolutions.com\" xmlns:xdp=\"http://www.adobe.com/xdp\" xmlns:xfa=\"http://www.adobe.com/xfa\" Id=\"440\" schemaVersion=\"4.0\">\r\n");
		emlXML.append("<TransactionId Id=\"" + transactionID + "\" />\r\n");
		emlXML.append("<CastVote>\r\n");
		emlXML.append("<EventIdentifier Id=\"State Of Connecticut - USA\" />\r\n");
		emlXML.append("<Election>\r\n");
		emlXML.append("<ElectionIdentifier Id=\"State Election - 2007\" />\r\n");
		Iterator itr = ballotLookupXMLMap.keySet().iterator();
		String key="";
		while(itr.hasNext()){
			key = (String)itr.next();
			logSB.append("ballotLookup Key "+key+" Value "+ballotLookupXMLMap.get(key));
		}
		writeFile(logSB.toString());
		String candidateID="",partyKey="";
		for(int i=1;i<=11;i++) {
			emlXML.append("<Contest>\r\n");
		    emlXML.append("<ContestIdentifier Id=\""+i+"\"/>\r\n");
		    for(int j=1;j<=7;j++) {
		    	partyKey="colID" + i + "checkID" + j;		    	
		    	emlXML.append("<Selection Shortcode=\"" + j	+ "\" Value=\"" + ballotXMLMap.get(partyKey)+ "\">\r\n");
		    	candidateID= (String) ballotLookupXMLMap.get(partyKey);
		    	emlXML.append("<CandidateIdentifier Id=\""+candidateID + "\" />\r\n");
		    	emlXML.append("<WriteinCandidateName />\r\n");
		    	emlXML.append("</Selection>\r\n");
		    }
		    emlXML.append("</Contest>\r\n");		
		}
		emlXML.append("</Election>\r\n");
		emlXML.append("</CastVote>\r\n");
		emlXML.append("</EML>\r\n");

		String eml440Folder = prop.getProperty("eml440Folder");
		System.out.println("eml440Folder " + eml440Folder);
		String fileName = "EML440_" + transactionID + ".xml";
		System.out.println("fileName " + fileName);
		writeFile(eml440Folder + fileName, emlXML.toString());		
}

	public void writeFile(String location, String output) {
		logSB.append("writeFile "+location+"\r\n");
		logSB.append("output lenth "+output.length()+"\r\n");
		writeFile(logSB.toString());

		try {
			FileOutputStream out = new FileOutputStream(location);			
			for (int i = 0; i < output.length(); i++) {
				out.write(output.charAt(i));
			}
			out.close();
		} catch (Exception e) {
			e.printStackTrace();
			logSB.append(e.toString());
			writeFile(logSB.toString());
		}
}
	  	
 public void parseBallotLookup(String s)
 {
	 logSB.append("inside the parseBallotLookup "+s+"\r\n");
	 writeFile(logSB.toString());
     BallotLookup ballotlookup = new BallotLookup();
     try
     {
         xmlString = ReadFile(s);
         System.out.print(xmlString);
         ballotLookupXMLMap = ballotlookup.getXMLMap(xmlString.toString().trim());
         xmlString = null;
     }
     catch(Exception exception)
     {
    	 logSB.append("Exception in parse Ballot Lookup... " + exception.getMessage());
    	 writeFile(logSB.toString());
         System.out.println("Exception in Ballot Lookup... " + exception.getMessage());
         exception.printStackTrace();
     }
 }

 public String ReadFile(String s)
     throws IOException
 {
     StringBuffer stringbuffer = new StringBuffer();
     try
     {
         BufferedReader bufferedreader = new BufferedReader(new FileReader(s));
         String s1;
         while((s1 = bufferedreader.readLine()) != null) 
             stringbuffer.append(s1.trim());
         bufferedreader.close();
     }
     catch(IOException ioexception) { }
     return stringbuffer.toString();
 }

 private boolean isMissing(String s)
 {
     return s == null || s.trim().equals("");
 }

 protected void makeWarning(HttpServletRequest httpservletrequest, String s)
 {
     MessageBean messagebean = (MessageBean)httpservletrequest.getAttribute("messageBean");
     messagebean.setMessage(s);
 }


}