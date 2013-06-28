package action;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Properties;
import java.util.Set;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import org.apache.struts.action.Action;
import org.apache.struts.action.ActionForm;
import org.apache.struts.action.ActionForward;
import org.apache.struts.action.ActionMapping;

import propmgr.PropertyLoader;
import util.BallotLookup;
import util.BallotXMLMap;
import util.Counting410Lookup;
import util.Counting510XMLMap;
import util.EMLXMLMap;
import util.MessageBean;
import valueobject.BallotVO;
import forms.CountingForm;

public class CountingAction extends Action
{
	StringBuffer logSB = new StringBuffer();
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
			
    	 	//  pl = new PropertyLoader("http://localhost:8080/iTalyVotingDemo/properties/application.properties");
			pl = new PropertyLoader("http://openvotingsolutions.info/iTalyVotingDemo/properties/application.properties");
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
         if(countingType.equals("ballotToEML440"))
         {
             System.out.print("ballotToEML440");
             logSB.append("inside ballotToEML440\r\n");
             countingform.setCountingType("eml440To510");
             String ballotLookupFolder = prop.getProperty("ballotLookupFolder");
             System.out.println("ballotLookupFolder " + ballotLookupFolder);
             logSB.append("ballotLookupFolder " + ballotLookupFolder+"\r\n");
             parseBallotLookup(ballotLookupFolder);
             try
             {
                 HashMap hashmap3 = new HashMap();
                 String ballotFolder = prop.getProperty("ballotFolder");
                 hashmap3 = readListofFiles(ballotFolder);
                 if(hashmap3 != null)
                 {
                     System.out.println("listOfEMLXMLs " + hashmap3.size());
                     logSB.append("listOfEMLXMLs " + hashmap3.size()+"\r\n");
                     Set set = hashmap3.keySet();
                     if(set != null)
                     {
                         for(Iterator iterator = set.iterator(); iterator.hasNext(); ballotvo.setTransactionDetails("Ballot to EML440 has been converted successfully...!"))
                         {
                             String s6 = (String)iterator.next();
                             xmlString = (String)hashmap3.get(s6);
                             BallotXMLMap ballotxmlmap = new BallotXMLMap();
                             HashMap hashmap1 = ballotxmlmap.getXMLMap(xmlString.toString().trim());
                             System.out.println("\r\n\r\nballotXMLMap Size " + hashmap1.size() + " ballotLookupXMLMap " + ballotLookupXMLMap.size());
                             logSB.append("\r\n\r\nballotXMLMap Size " + hashmap1.size() + " ballotLookupXMLMap " + ballotLookupXMLMap.size()+"\r\n");
                             xmlString = null;
                             generateEML440(hashmap1, ballotLookupXMLMap);
                             hashmap1 = new HashMap();
                         }

                     }
                 }
             }
             catch(Exception exception2)
             {
                 System.out.println("Exception in Ballot..." + exception2.getMessage());
                 logSB.append("Exception in Ballot..." + exception2.getMessage()+"\r\n");
                 writeFile(logSB.toString());
                 ballotvo.setTransactionDetails(exception2.toString());
             }
         }
         if(countingType.equals("eml440To510"))
         {
             System.out.print("eml440To510");
             logSB.append("inside the eml440To510 if condition\r\n");
             countingform.setCountingType("eml510To520");
             HashMap hashmap2 = new HashMap();
             hashmap2 = getEMLXMLCountingDataMap();
             System.out.println("hashmap2 "+hashmap2.size());
             generateEML510(hashmap2);
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
//    	 FileOutputStream fileoutputstream = new FileOutputStream("C:/Tomcat 5.0/webapps/iTalyVotingDemo/counting-ovs.log");
    	 FileOutputStream fileoutputstream = new FileOutputStream("/home/ovsadmin/public_html/iTalyVotingDemo/ovs-counting.log");
         
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
     StringBuffer stringbuffer = new StringBuffer();
     stringbuffer.append("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n");
     stringbuffer.append("<?xml-stylesheet type=\"text/xsl\" href=\"http://openvotingsolutions.info/iTalyVotingDemo/xml/eml520result/ovs-EML520-results.xsl\"?>\r\n");
     stringbuffer.append("<EML xmlns:ovs=\"http://www.openvotingsolutions.com\" Id=\"520\" SchemaVersion=\"4.0\">\r\n");
     stringbuffer.append("<TransactionId>2006-09-12</TransactionId>\r\n");
     stringbuffer.append("<Result>\r\n");
     stringbuffer.append("<Election>\r\n");
     stringbuffer.append("<EventIdentifier Id=\"ITALY\" />\r\n");
     stringbuffer.append("<Contest>\r\n");
     stringbuffer.append("<ContestIdentifier Id=\"District Election - 2007\" />\r\n");
     String s = "CandidateName";
     String s1 = "RegisteredName";
     int i = 1;
     if(countingXMLMap != null)
     {
         Set set = countingXMLMap.keySet();
         if(set != null)
         {
             for(Iterator iterator = set.iterator(); iterator.hasNext();)
             {
                 String s3 = (String)iterator.next();
                 System.out.println("countingXMLMap val " + countingXMLMap.get(s3));
                 stringbuffer.append("<Selection>\r\n");
                 stringbuffer.append("<CandidateIdentifier ID=\"" + s3 + "\" DisplayOrder=\"" + i + "\">\r\n");
                 stringbuffer.append("<CandidateName>" + countingLookupXMLMap.get(s3 + s) + "</CandidateName>\r\n");
                 stringbuffer.append("</CandidateIdentifier>\r\n");
                 stringbuffer.append("<Affiliation>\r\n");
                 stringbuffer.append("<AffiliationIdentifier ID=\"DEM\">\r\n");
                 stringbuffer.append("<RegisteredName>" + countingLookupXMLMap.get(s3 + s1) + "</RegisteredName>\r\n");
                 stringbuffer.append("</AffiliationIdentifier>\r\n");
                 stringbuffer.append("</Affiliation>\r\n");
                 stringbuffer.append("<Votes>" + countingXMLMap.get(s3) + "</Votes>\r\n");
                 stringbuffer.append("</Selection>\r\n");
                 i++;
             }

         }
     }
     stringbuffer.append("</Contest>\r\n");
     stringbuffer.append("</Election>\r\n");
     stringbuffer.append("</Result>\r\n");
     stringbuffer.append("</EML>\r\n");
     String s2 = prop.getProperty("eml520ResultFolder");
     writeFile(s2, stringbuffer.toString());
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

 public void generateEML510(HashMap hashmap)
 {
	 logSB.append("Inside the generateEML510");
     StringBuffer stringbuffer = new StringBuffer();
     stringbuffer.append("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n");
     stringbuffer.append(" <EML Id=\"510\" schemaVersion=\"4.0\">\r\n");
     stringbuffer.append("<EventIdentifier Id=\"Italy Voting\" />\r\n");
     stringbuffer.append("<Election>\r\n");
     stringbuffer.append("<ElectionIdentifier Id=\"District Election \" />\r\n");
     stringbuffer.append("<Contest>\r\n");
     stringbuffer.append("<ContestIdentifier>2006</ContestIdentifier>\r\n");
     stringbuffer.append("<TotalVotes>\r\n");
     if(hashmap != null)
     {
         Set set = hashmap.keySet();
         if(set != null)
         {
             for(Iterator iterator = set.iterator(); iterator.hasNext(); stringbuffer.append("</Selection>\r\n"))
             {
                 String s1 = (String)iterator.next();
                 System.out.println("Eml key " + s1 + " Value " + hashmap.get(s1) + "\r\n");
                 stringbuffer.append("<Selection>\r\n");
                 stringbuffer.append("<CandidateIdentifier ID=\"" + s1 + "\"/>\r\n");
                 stringbuffer.append("<ValidVotes>" + hashmap.get(s1) + "</ValidVotes>\r\n");
             }

         }
     }
     stringbuffer.append("</TotalVotes>\r\n");
     stringbuffer.append("</Contest>\r\n");
     stringbuffer.append("</Election>\r\n");
     stringbuffer.append("</EML>\r\n");
     String eml510CountingFolder = prop.getProperty("eml510CountingFolder");
     logSB.append("eml510CountingFolder in gen "+eml510CountingFolder+"\r\n");
     writeFile(logSB.toString());
     writeFile(eml510CountingFolder, stringbuffer.toString());
 }

 public HashMap getEMLXMLCountingDataMap() {
		HashMap listOfEMLXMLs = new HashMap();
		HashMap emlXMLMap = new HashMap();
		int oldVal = 0, newVal = 0, setVal = 0;
		String xmlString = null;
		String oldValS;
		String newValS;
		String eml440Folder = prop.getProperty("eml440Folder");
		
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
										oldValS=emlXMLMap.get(newkey).toString();
										newValS=mapNew.get(newkey).toString();
										System.out.println("oldVal "+oldValS+" "+oldValS.length());
										System.out.println("newVal "+newValS+" "+newValS.length());
										oldVal = Integer.parseInt(oldValS);
										newVal = Integer.parseInt(newValS);
										setVal = oldVal + newVal;
										System.out.println("Set Val " + setVal);
										emlXMLMap.put(newkey, new Integer(setVal));
									} else {
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

 public void generateEML440(HashMap hashmap, HashMap hashmap1)
 {
     String ballotTransactionID = (String)hashmap.get("ballotTransactionID");
     System.out.print("\r\ntransactionID " + ballotTransactionID);
     StringBuffer stringbuffer = new StringBuffer();
     HashMap hashmap2 = new HashMap();
     HashMap hashmap3 = new HashMap();
     HashMap hashmap4 = new HashMap();
     stringbuffer.append("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n");
     stringbuffer.append("<EML xmlns:ovs=\"http://www.openvotingsolutions.com\" xmlns:xdp=\"http://www.adobe.com/xdp\" xmlns:xfa=\"http://www.adobe.com/xfa\" Id=\"440\" schemaVersion=\"4.0\">\r\n");
     stringbuffer.append("<TransactionId Id=\"" + ballotTransactionID + "\" />\r\n");
     stringbuffer.append("<CastVote>\r\n");
     stringbuffer.append("<EventIdentifier Id=\"Italy Voting\" />\r\n");
     stringbuffer.append("<Election>\r\n");
     stringbuffer.append("<ElectionIdentifier Id=\"District Election - 2006\" />\r\n");
     String s1 = "rID1cID";
     String s2 = "rID2cID";
     String s3 = "rID3cID";
     if(hashmap != null)
     {
         Set set = hashmap.keySet();
         if(set != null)
         {
             Iterator iterator = set.iterator();
             do
             {
                 if(!iterator.hasNext())
                     break;
                 String s8 = (String)iterator.next();
                 if(s8.startsWith(s1))
                     hashmap2.put(s8, hashmap.get(s8));
                 else
                 if(s8.startsWith(s2))
                     hashmap3.put(s8, hashmap.get(s8));
                 else
                 if(s8.startsWith(s3))
                     hashmap4.put(s8, hashmap.get(s8));
             } while(true);
         }
     }
     System.out.print("\r\nballotSide1Map " + hashmap2.size() + " ballotSide2Map " + hashmap3.size() + " ballotSide3Map " + hashmap4.size());
     hashmap = new HashMap();
     Object obj = null;
     stringbuffer.append("<Contest>\r\n");
     stringbuffer.append("<ContestIdentifier>Row1</ContestIdentifier>\r\n");
     if(hashmap2 != null)
     {
         Set set1 = hashmap2.keySet();
         if(set1 != null)
         {
             for(Iterator iterator1 = set1.iterator(); iterator1.hasNext(); stringbuffer.append("</Selection>\r\n"))
             {
                 String s10 = (String)iterator1.next();
                 String s4 = s10.substring(s1.length(), s10.length());
                 stringbuffer.append("<Selection Shortcode=\"" + s4 + "\" Value=\"" + hashmap2.get(s10) + "\">\r\n");
                 stringbuffer.append("<CandidateIdentifier Id=\"" + hashmap1.get(s10) + "\" />\r\n");
                 stringbuffer.append("<WriteinCandidateName></WriteinCandidateName>\r\n");
             }

         }
     }
     stringbuffer.append("</Contest>\r\n");
     hashmap2 = new HashMap();
     stringbuffer.append("<Contest>\r\n");
     stringbuffer.append("<ContestIdentifier>Row2</ContestIdentifier>\r\n");
     if(hashmap3 != null)
     {
         Set set2 = hashmap3.keySet();
         if(set2 != null)
         {
             for(Iterator iterator2 = set2.iterator(); iterator2.hasNext(); stringbuffer.append("</Selection>\r\n"))
             {
                 String s11 = (String)iterator2.next();
                 String s5 = s11.substring(s2.length(), s11.length());
                 stringbuffer.append("<Selection Shortcode=\"" + s5 + "\" Value=\"" + hashmap3.get(s11) + "\">\r\n");
                 stringbuffer.append("<CandidateIdentifier Id=\"" + hashmap1.get(s11) + "\" />\r\n");
                 stringbuffer.append("<WriteinCandidateName></WriteinCandidateName>\r\n");
             }

         }
     }
     stringbuffer.append("</Contest>\r\n");
     hashmap3 = new HashMap();
     stringbuffer.append("<Contest>\r\n");
     stringbuffer.append("<ContestIdentifier>Row3</ContestIdentifier>\r\n");
     if(hashmap4 != null)
     {
         Set set3 = hashmap4.keySet();
         if(set3 != null)
         {
             for(Iterator iterator3 = set3.iterator(); iterator3.hasNext(); stringbuffer.append("</Selection>\r\n"))
             {
                 String s12 = (String)iterator3.next();
                 String s6 = s12.substring(s3.length(), s12.length());
                 stringbuffer.append("<Selection Shortcode=\"" + s6 + "\" Value=\"" + hashmap4.get(s12) + "\">\r\n");
                 stringbuffer.append("<CandidateIdentifier Id=\"" + hashmap1.get(s12) + "\" />\r\n");
                 stringbuffer.append("<WriteinCandidateName></WriteinCandidateName>\r\n");
             }

         }
     }
     stringbuffer.append("</Contest>\r\n");
     hashmap4 = new HashMap();
     stringbuffer.append("</Election>\r\n");
     stringbuffer.append("</CastVote>\r\n");
     stringbuffer.append("</EML>\r\n");
     String eml440Folder = prop.getProperty("eml440Folder");
     System.out.println("\r\neml440Folder " + eml440Folder);
     String fileName = "EML440_" + ballotTransactionID + ".xml";
     System.out.println("\r\nfileName " + fileName);
 	logSB.append("eml440Folder in gen440 "+eml440Folder+"\r\n");
	logSB.append("fileName "+fileName+"\r\n");
	writeFile(logSB.toString());
    writeFile(eml440Folder+fileName, stringbuffer.toString());
     
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
     BallotLookup ballotlookup = new BallotLookup();
     try
     {
         xmlString = ReadFile(s);
         ballotLookupXMLMap = ballotlookup.getXMLMap(xmlString.toString().trim());
         xmlString = null;
     }
     catch(Exception exception)
     {
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

 PropertyLoader pl;
 Properties prop;
 public String xmlString;
 public HashMap ballotLookupXMLMap;
 public HashMap countingLookupXMLMap;
 public HashMap countingXMLMap;
}