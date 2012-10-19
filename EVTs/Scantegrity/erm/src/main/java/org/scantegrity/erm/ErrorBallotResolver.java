package org.scantegrity.erm;

import java.awt.Rectangle;
import java.awt.image.BufferedImage;
import java.beans.XMLEncoder;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.TreeMap;
import java.util.Vector;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.apache.commons.io.FileUtils;
import org.scantegrity.common.Ballot;
import org.scantegrity.common.BallotStyle;
import org.scantegrity.common.Contest;
import org.scantegrity.common.Contestant;
import org.scantegrity.common.RandomBallotStore;
import org.scantegrity.common.methods.ContestChoice;
import org.scantegrity.common.methods.ContestResult;
import org.scantegrity.common.methods.TallyMethod;
import org.scantegrity.erm.WriteInResolver.WriteInResolution;
import org.scantegrity.scanner.ScannerConfig;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.itextpdf.text.log.Level;
import com.lowagie.text.DocumentException;
import com.lowagie.text.pdf.PdfPTable;
import com.lowagie.text.pdf.PdfWriter;

/* This class loads in ballots and uses a queue to pull up all the write-in positions that need to be
 * resolved.
 */

public class ErrorBallotResolver {
	
	private Map<Integer, BallotStyle> c_ballotStyles = null;
	private Map<Integer, ContestQueue> c_locations = null;
	private Contest c_currentContest = null;
	private ScannerConfig c_config = null;
	private ErrorBallotLocation c_currentLocation = null;
	private TreeMap<Integer, Vector<ContestChoice>> c_contestChoices = null;
	private TreeMap<Integer, Vector<ContestChoice>> c_unalteredChoices = null;
	private Vector<ErrorBallotResolution> c_resolutions = null;
	private HashSet<Integer> c_usedIds = null;
	private SecureRandom c_random = null;
	private int c_errorCount = 0;
	private boolean c_enableResolve = true;
	private ERM c_erm = null;
	private HashMap<Integer, Contest> c_errorContests;
	private WriteInResolver c_writeinResolver = null;
	
	
	//Represents a resolution that was done by the user.  Used for the resolution pdf.
	class ErrorBallotResolution
	{
		public BufferedImage image;
		public String id;
		public Contest contest;
		public Integer[][] contestData;
		public Object choice; 
		
		public ErrorBallotResolution(BufferedImage p_image, String p_contest_id, Integer[][] p_contestData)
		{
			image = p_image;
			id = p_contest_id;
			contestData = p_contestData; 
		}
	}
	
	class ErrorBallotLocation
	{
		public Ballot ballot;
		public int contestId;
		Vector<String> errorsFound; 
		public ErrorBallotLocation(Ballot p_ballot, int p_contestId, Vector<String> p_errorsFound)
		{
			ballot = p_ballot;
			contestId = p_contestId;
			errorsFound = p_errorsFound;
		}
	}
	
	class ContestQueue
	{
		public int contestId;
		public Queue<ErrorBallotLocation> queue;
		public String contestName;
		public ContestQueue(int p_id, String p_name)
		{
			queue = new LinkedList<ErrorBallotLocation>();
			contestName = p_name;
		}
	}
	
	public ErrorBallotResolver(ScannerConfig p_config, boolean p_enableResolve, ERM p_erm, WriteInResolver p_writeinResolver)
	{
		this(p_config, p_erm, p_writeinResolver);
		c_enableResolve = p_enableResolve;
		c_writeinResolver = p_writeinResolver;
	}
	
	public ErrorBallotResolver(ScannerConfig p_config, ERM p_erm, WriteInResolver p_writeinResolver)
	{
		c_config = p_config;
		c_erm  = p_erm; 
		Vector<BallotStyle> l_styles = c_config.getStyles();
		c_contestChoices = new TreeMap<Integer, Vector<ContestChoice>>();
		c_unalteredChoices = new TreeMap<Integer, Vector<ContestChoice>>();
		c_locations = new TreeMap<Integer, ContestQueue>();
		c_resolutions = new Vector<ErrorBallotResolution>();
		c_writeinResolver = p_writeinResolver;
		
		c_random = new SecureRandom();
		
		c_ballotStyles = new HashMap<Integer, BallotStyle>();
		for( BallotStyle l_style : l_styles )
		{
			c_ballotStyles.put(l_style.getId(), l_style);
		}
		
		Vector<Contest> l_contests = c_config.getContests();
		c_errorContests = new HashMap<Integer, Contest>();
		
		for( Contest l_contest : l_contests )
		{
			c_errorContests.put(l_contest.getId(), l_contest);
		}
		
	}
	
	//1) Finds ballot stores on all removable disks
	//2) Reads ballots from each store and figures out which ballot positions need to be resolved
	//3) Adds each ballot position to a queue for the user to resolve
	public int LoadBallots(RandomBallotStore p_store) throws IOException {
			Vector<Ballot> l_ballots;
			l_ballots = p_store.getBallots();
			System.out.println("Loading " + l_ballots.size() + " ballots...");
			return ParseBallots(l_ballots);
	}
	
	// The BallotStorePanel uses this. 
	public int unloadBallots(RandomBallotStore p_store) throws IOException {
		Vector<Ballot> l_ballots;
		l_ballots = p_store.getBallots();
		System.out.println("Unloading " + l_ballots.size() + " ballots...");
		
		int l_x = 0; //TODO: Is this counting contests?
		for( Ballot l_ballot : l_ballots )
		{
			Map<Integer, Vector<String>> l_error_contests = l_ballot.getErrorContests();
			l_x++;
			
			// if we dont have any errors in this ballot, continue on
			if (l_error_contests == null)
				continue; 
			
			//we have errors, get the info we need. 
			
			BallotStyle l_style = c_ballotStyles.get(l_ballot.getBallotStyleID());
			Vector<Integer> l_contestIds = l_style.getContests();  
			
			//Look in each contest for write-ins
			for( Integer l_contestId : l_contestIds )
			{
				Contest l_contest = c_errorContests.get(l_contestId);
				Integer[][] l_contestData = l_ballot.getContestData(l_contestId);
				if( l_contestData == null )
				{
					//System.out.println("NULL BALLOT!");
					//System.out.println("ID: " + l_ballot.getId());
					continue;
				}
				
				if( !c_enableResolve )
					continue;
				
				if (l_error_contests.containsKey(l_contestId)) { 
					//There are errors for this contest
					if (c_locations.containsKey(l_contestId)) {
						c_locations.get(l_contestId).queue.add(new ErrorBallotLocation(l_ballot, l_contestId, l_error_contests.get(l_contestId)));
					}
					else
					{
						ContestQueue l_newQueue = new ContestQueue(l_contestId, l_contest.getContestName());
						l_newQueue.queue.add(new ErrorBallotLocation(l_ballot, l_contestId, l_error_contests.get(l_contestId)));
						c_locations.put(l_contestId, l_newQueue);
					}
					c_errorCount++;
				}
			}
		}
		return l_x;
	}

	/* 
	 * For each ballot, see if there are voting errors we need to resolve and 
	 * if found, add them to a Queue. 
	 */
	private int ParseBallots(Vector<Ballot> p_ballots) {
		int l_x = 0; //This counts the number of ballots. 
		for( Ballot l_ballot : p_ballots )
		{
			Map<Integer, Vector<String>> l_error_contests = l_ballot.getErrorContests();
			l_x++;
			
			// if we dont have any errors in this ballot, continue on
			if (l_error_contests == null) { 
				continue; 
			}
			
			//we have errors, get the info we need. 
			
			BallotStyle l_style = c_ballotStyles.get(l_ballot.getBallotStyleID());
			Vector<Integer> l_contestIds = l_style.getContests();  
			
			//Look in each contest for write-ins
			for( Integer l_contestId : l_contestIds )
			{
				Contest l_contest = c_errorContests.get(l_contestId);
				Integer[][] l_contestData = l_ballot.getContestData(l_contestId);
				if( l_contestData == null )
				{
					//System.out.println("NULL BALLOT!");
					//System.out.println("ID: " + l_ballot.getId());
					continue;
				}
				
				if( !c_enableResolve )
					continue;
				
				if (l_error_contests.containsKey(l_contestId)) { 
					//There are errors for this contest
					if (c_locations.containsKey(l_contestId)) {
						c_locations.get(l_contestId).queue.add(new ErrorBallotLocation(l_ballot, l_contestId, l_error_contests.get(l_contestId)));
					}
					else
					{
						ContestQueue l_newQueue = new ContestQueue(l_contestId, l_contest.getContestName());
						l_newQueue.queue.add(new ErrorBallotLocation(l_ballot, l_contestId, l_error_contests.get(l_contestId)));
						c_locations.put(l_contestId, l_newQueue);
					}
					c_errorCount++;
				}
			}
		}
		return l_x;
	}

	public boolean next() {
		c_currentLocation = null;
		for( int x = 0; x < c_errorContests.size() && c_currentLocation == null; x++ )
		{
			int l_id = c_errorContests.get(x).getId();
			if( c_locations.containsKey(l_id) && c_locations.get(l_id).queue.peek() != null )
			{
				c_currentLocation = c_locations.get(l_id).queue.poll();
			}
		}
		if( c_currentLocation == null ) { 
			return false;
		}
		c_currentContest = c_errorContests.get(c_currentLocation.contestId);
		return true;
	}

	public BufferedImage getImage() {
		Ballot l_curBallot = c_currentLocation.ballot;
		return l_curBallot.getImage(); 
	}
	
	public void Resolve(Integer[][] p_contestData) {		
		ErrorBallotResolution l_res = null;
		l_res = new ErrorBallotResolution(getImage(), Integer.toString(c_currentLocation.contestId), p_contestData);
		l_res.contest = c_currentContest;
		int l_ballotId = c_currentLocation.ballot.getId();
		
		c_writeinResolver.addContestData(c_currentContest, p_contestData, l_ballotId);
		
		if( l_res != null )
			c_resolutions.add(l_res);
		
		
		/* Debug: Prints the new contest data from the resolver * /
		System.out.println("Results: "); 
		for (int i = 0; i < p_contestData.length; i++) { 
			for (int j = 0; j < p_contestData[i].length; j++) { 
				System.out.print("\t" + p_contestData[i][j]); 
			}
			System.out.print("\n");
		}
		/* End Debug */
	}
	
	@SuppressWarnings("unchecked")
	public void WriteResults(String p_outDir) {
		File l_outDir = new File(p_outDir);
		
		Collection l_files = FileUtils.listFiles(l_outDir, new String[]{"sbr"}, false);
		TreeMap<Integer, BufferedWriter> l_writers = new TreeMap<Integer, BufferedWriter>();
		
		Iterator l_iterator = l_files.iterator();
		
		while(l_iterator.hasNext())
		{
			File l_file = (File)l_iterator.next();
			try {
				RandomBallotStore l_store = new RandomBallotStore(0, 0, 0, l_file.getPath(), null, null);
				l_store.open();
				Vector<Ballot> l_ballots = l_store.getBallots();
				for( Ballot l_ballot : l_ballots )
				{
					if( !l_writers.containsKey(l_ballot.getBallotStyleID()) )
					{
						File l_newDir = new File(l_outDir, "Ward" + l_ballot.getBallotStyleID());
						if( !l_newDir.exists() )
							l_newDir.mkdir();
						BufferedWriter l_writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(new File(l_newDir, "MeetingThreeIn.xml"))));
						l_writers.put(l_ballot.getBallotStyleID(), l_writer);
						l_writer.write("<xml>\n\t<print>\n");
					}
					
					BufferedWriter l_writer = l_writers.get(l_ballot.getBallotStyleID());
					
					if (l_ballot.isCounted())
					{
						String l_ballotId = l_ballot.getId().toString();
						l_ballotId = l_ballotId.substring(1);
						l_writer.write("\t\t<row id=\"" + Integer.parseInt(l_ballotId) + "\" p3=\"");
						String l_tmp = "";
						
						BallotStyle l_style = c_ballotStyles.get(l_ballot.getBallotStyleID());
						for (Integer l_cId : l_style.getContests())
						{
							Contest l_c = c_errorContests.get(l_cId);
							if (l_ballot.hasContest(l_c.getId()))
							{
								Integer l_data[][] = l_ballot.getContestData(l_c.getId());
								//For each column
								for (int l_i = 0; l_i < l_data[0].length; l_i++)
								{
									Vector<Integer> l_cans = new Vector<Integer>();
									//Each contestant
									for (int l_j = 0; l_j < l_data.length; l_j++)
									{
										if (l_data[l_j][l_i] == 1)
										{
											l_cans.add(l_j);
										}
									}
									if (l_cans.size() != 1) l_tmp += -1;
									else l_tmp += l_cans.get(0);
									l_tmp += " ";
								}
							}
						}
						l_writer.write( l_tmp.substring(0, l_tmp.length()-1) );
						l_writer.write( "\" page=\"NONE\"/>\n" );
					}
				}
			} catch (NoSuchAlgorithmException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		
		while( !l_writers.isEmpty() )
		{
			BufferedWriter l_writer = l_writers.pollFirstEntry().getValue();
			try {
				l_writer.write("\t</print>\n</xml>");
				l_writer.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}
	
	public void Tally(String p_outDir) {
		//if( c_enableResolve )
		//	return;
		System.out.println("Tallying " + c_contestChoices.size() + " mappings...");
		
		try {
			File l_siteDir = new File(new File(p_outDir), "Website");
			
			if( !l_siteDir.exists() )
				l_siteDir.mkdir();
			
			XMLEncoder l_enc = new XMLEncoder(new FileOutputStream(new File(l_siteDir, "ContestChoices.xml")));
			l_enc.writeObject(c_contestChoices);
			l_enc.close();
			
			l_enc = new XMLEncoder(new FileOutputStream(new File(l_siteDir, "NonResolvedContestChoices.xml")));
			l_enc.writeObject(c_unalteredChoices);
			l_enc.close();
			
			l_enc = new XMLEncoder(new FileOutputStream(new File(l_siteDir, "ScannerConfig.xml")));
			l_enc.writeObject(c_config);
			l_enc.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		File l_newDir = new File(new File(p_outDir), "Results");
		if( !l_newDir.exists() )
			l_newDir.mkdir();
		
		
		while( !c_contestChoices.isEmpty() )
		{
			Integer l_key = c_contestChoices.firstKey();
			
			Vector<ContestChoice> l_choices = c_contestChoices.get(l_key);
			Collections.shuffle(l_choices, new SecureRandom());
			c_contestChoices.remove(l_key);
			
			Vector<ContestChoice> l_shortChoices = c_unalteredChoices.get(l_key);
			Collections.shuffle(l_choices, new SecureRandom());
			c_unalteredChoices.remove(l_key);
			
			//Tally without Write-Ins
			Contest l_curContest = c_errorContests.get(l_key);
			
			TallyMethod l_method = l_curContest.getTallyMethod();
			ContestResult l_result = l_method.tally(l_curContest, l_shortChoices);
			
			//print out results to file
			FileWriter l_outStream = null;
			try {
				l_outStream = new FileWriter(new File(l_newDir, "results.txt"), true);
				l_outStream.write(l_curContest.getContestName()+ "\n\n");
				l_outStream.write(l_result.toString());
				l_outStream.close();
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			
			WriteContestResults(l_result, l_curContest, l_shortChoices, new File(l_newDir, l_curContest.getShortName() + ".xml").getPath());
			
			
			//Tally with Write-Ins
			Contest l_writeInContest = c_errorContests.get(l_key);
			
			TallyMethod l_writeInMethod = l_writeInContest.getTallyMethod();
			ContestResult l_writeInResult = l_writeInMethod.tally(l_writeInContest, l_choices);
			
			//print out results to file
			l_outStream = null;
			try {
				l_outStream = new FileWriter(new File(l_newDir, "writein-results.txt"), true);
				l_outStream.write(l_writeInContest.getContestName()+ "\n\n");
				l_outStream.write(l_writeInResult.toString());
				l_outStream.close();
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
			
			WriteContestResults(l_writeInResult, l_writeInContest, l_choices, new File(l_newDir, l_writeInContest.getShortName() + "Short.xml").getPath());
		}
	}
	
	private void WriteContestResults(ContestResult p_result, Contest p_contest, Vector<ContestChoice> p_choices, String p_out) {		
		TreeMap<Integer, Vector<Contestant>> l_rankings = p_result.getRanking();

		DocumentBuilderFactory l_factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder l_builder = null;
		try {
			l_builder = l_factory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			e.printStackTrace();
			return;
		}
		Document l_doc = l_builder.newDocument();
		
		Element l_root = l_doc.createElement("Results");
		l_doc.appendChild(l_root);
		
		Element l_contestNode = l_doc.createElement("Contest");
		l_root.appendChild(l_contestNode);
		
		Element l_contestNameNode = l_doc.createElement("Name");
		l_contestNameNode.appendChild(l_doc.createTextNode(p_contest.getContestName()));
		l_contestNode.appendChild(l_contestNameNode);
		
		Element l_contestIdNode = l_doc.createElement("ID");
		l_contestIdNode.appendChild(l_doc.createTextNode(p_contest.getId().toString()));
		l_contestNode.appendChild(l_contestIdNode);
		
		Element l_tallyMethodNode = l_doc.createElement("TallyMethod");
		l_tallyMethodNode.appendChild(l_doc.createTextNode(p_contest.getTallyMethod().getClass().toString()));
		l_contestNode.appendChild(l_tallyMethodNode);
		
		Element l_contestants = l_doc.createElement("Contestants");
		l_contestNode.appendChild(l_contestants);
		
		for( Contestant l_contestant : p_contest.getContestants() )
		{
			Element l_contestantNode = l_doc.createElement("Contestant");
			l_contestants.appendChild(l_contestantNode);
			
			Element l_contestantNameNode = l_doc.createElement("Name");
			l_contestantNameNode.appendChild(l_doc.createTextNode(l_contestant.getName()));
			l_contestantNode.appendChild(l_contestantNameNode);
			
			Element l_contestantIdNode = l_doc.createElement("ID");
			l_contestantIdNode.appendChild(l_doc.createTextNode(l_contestant.getId().toString()));
			l_contestantNode.appendChild(l_contestantIdNode);
		}
		
		Element l_votesNode = l_doc.createElement("Votes");
		l_root.appendChild(l_votesNode);
		
		for( ContestChoice l_choice : p_choices )
		{
			Element l_voteNode = l_doc.createElement("Vote");
			l_votesNode.appendChild(l_voteNode);
			
			int[][] l_data = l_choice.getChoices();
			for( int x = 0; x < l_data.length; x++ )
			{
				Element l_rankNode = l_doc.createElement("Rank");
				l_rankNode.setAttribute("id", x + "");
				String l_rankValue = "";
				for( int y = 0; y < l_data[x].length; y++ )
				{
					l_rankValue += Integer.toString(l_data[x][y]);
					if( y != l_data[x].length - 1 )
					{
						l_rankValue += " ";
					}
				}
				l_rankNode.appendChild(l_doc.createTextNode(l_rankValue));
				l_voteNode.appendChild(l_rankNode);
			}
		}
		
		Element l_resultsNode = l_doc.createElement("Results");
		l_root.appendChild(l_resultsNode);
		
		Integer l_key = l_rankings.firstKey();
		while(l_key != null)
		{
			Element l_rankNode = l_doc.createElement("Rank");
			l_rankNode.setAttribute("id", Integer.toString(l_key));
			l_resultsNode.appendChild(l_rankNode);
			
			Vector<Contestant> l_candidates = l_rankings.get(l_key);
			for( Contestant l_contestant : l_candidates )
			{
				Element l_contestantNode = l_doc.createElement("Contestant");
				l_rankNode.appendChild(l_contestantNode);
				
				Element l_contestantNameNode = l_doc.createElement("Name");
				l_contestantNameNode.appendChild(l_doc.createTextNode(l_contestant.getName()));
				l_contestantNode.appendChild(l_contestantNameNode);
				
				Element l_contestantIdNode = l_doc.createElement("ID");
				l_contestantIdNode.appendChild(l_doc.createTextNode(Integer.toString(l_contestant.getId())));
				l_contestantNode.appendChild(l_contestantIdNode);
				
				
			}
			l_key = l_rankings.higherKey(l_key);
		}
		
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
        Transformer transformer;
		try {
			transformer = transformerFactory.newTransformer();
			transformer.setOutputProperty("indent", "yes");
	        DOMSource source = new DOMSource(l_doc);
	        FileOutputStream l_out = new FileOutputStream(p_out);
	        StreamResult result =  new StreamResult(l_out);
	        transformer.transform(source, result);
	        l_out.close();
		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}
	
	public void WriteResolutionPdf(String p_outDir) {
		if( c_resolutions.isEmpty() ) { 
			System.out.println("No error resolutions to print.");
			return;
		}
		
		com.lowagie.text.Document l_doc = new com.lowagie.text.Document();
		com.lowagie.text.Image l_img;
		String l_formatString = "Contest Name: %s\nContest Data: \n%s";
		
		//Make sure we don't overwrite previous saves.
		try {
			PdfWriter.getInstance(l_doc, new FileOutputStream(p_outDir + File.separator + "ErrorResolves.pdf"));
			l_doc.open();
			PdfPTable l_table = new PdfPTable(2);
			for( ErrorBallotResolution l_res : c_resolutions )
			{
				l_img = com.lowagie.text.Image.getInstance(l_res.image.getScaledInstance(510, 660, BufferedImage.SCALE_DEFAULT), null);
				l_table.addCell(l_img);
				
				String l_contestData = "";  
				for (int i = 0; i < l_res.contestData.length; i++) { 
					for (int j = 0; j < l_res.contestData[i].length; j++) { 
						l_contestData += l_res.contestData[i][j] + " "; 
					}
					l_contestData += "\n"; 
				}
				l_table.addCell(String.format(l_formatString, l_res.contest.getContestName(), l_contestData));
			}
			l_doc.add(l_table);
			com.lowagie.text.Phrase l_phrase = new com.lowagie.text.Phrase();
			com.lowagie.text.Paragraph l_para = new com.lowagie.text.Paragraph("Judge Signature _____________");
			l_phrase.add(l_para);
			com.lowagie.text.HeaderFooter l_footer = new com.lowagie.text.HeaderFooter(l_phrase, true);
			l_doc.setFooter(l_footer);
			l_doc.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (DocumentException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}		
	}
	
	public Integer[][] getContestData() { 
		return c_currentLocation.ballot.getContestData(c_currentLocation.contestId); 
	}
	
	public String getContestName() {
		return c_currentContest.getContestName();
	}
	
	public int getErrorBallotCount() {
		return c_errorCount;
	}

	public void disableTabs() {
		c_erm.disableTabs();
	}

	public Vector<String> getErrorStrings() {
		return c_currentLocation.errorsFound; 
	}

}
