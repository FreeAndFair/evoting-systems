package org.scantegrity.sws.action;

import java.beans.XMLDecoder;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Map;
import java.util.TreeMap;
import java.util.Vector;
import java.util.zip.ZipEntry;
import java.util.zip.ZipOutputStream;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import net.sourceforge.stripes.action.DefaultHandler;
import net.sourceforge.stripes.action.FileBean;
import net.sourceforge.stripes.action.ForwardResolution;
import net.sourceforge.stripes.action.Resolution;
import net.sourceforge.stripes.validation.Validate;

import org.scantegrity.common.*;
import org.scantegrity.common.methods.*;
import org.scantegrity.scanner.*;
import org.scantegrity.sws.action.DAOFactory;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

public class FileuploadActionBean extends RestrictedActionBean {	
	@Validate(required=true) FileBean c_file;
	int c_styleId;
	String c_result = "";
	String c_error = "";
	
	public int getStyleId()
	{
		return c_styleId;
	}
	
	public void setStyleId(int p_styleId)
	{
		c_styleId = p_styleId;
	}

	public FileBean getFile()
	{
		return c_file;
	}

	public void setFile(FileBean p_file)
	{
		c_file = p_file;
	}

	public String getResult()
	{
		return c_result;
	}

	public void setResult(String p_text)
	{
		c_result = "<div class=\"results\">" + p_text + "</div>";
	}

	public String getErrors()
	{
		return "<div class=\"error\">" + c_error + "</div>";
	}

	public void setErrors(String p_error)
	{
		c_error = p_error;
	}

	@DefaultHandler
	public Resolution submit()
	{
		Resolution l_userCheck = super.checkUser();
		if( l_userCheck != null ) return l_userCheck;
		
		System.setProperty("derby.system.home", "/opt/db-derby");
		if( c_file != null )
		{
			if( c_file.getFileName().contains("MeetingThreeOutCodes.xml") )
			{
				parseCodes();
			}
			else if( c_file.getFileName().equals("ContestChoices.xml") )
			{
				parseChoices(true);
			}
			else if( c_file.getFileName().equals("NonResolvedContestChoices.xml"))
			{
				parseChoices(false);
			}
			
			saveFile();
		}

		return new ForwardResolution("/WEB-INF/pages/fileupload.jsp");
	}
	
	public void saveFile()
	{
		try
		{
			File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
			if( !l_docsDir.exists() )
			{
				throw new FileNotFoundException("Docs folder could not be found");
			}
			File l_saveFile = new File(l_docsDir.getPath() + File.separator + c_file.getFileName());
			c_file.save(l_saveFile);
			
			if( c_file.getFileName().contains(".xml") )
			{
				ZipThread c_zip = new ZipThread(l_docsDir);
				c_zip.start();
			}
			c_result = "File saved successfully";
		}
		catch(IOException e)
		{
			c_error += e.getMessage() + "\n";
		}
	}
	
	public void parseCodes()
	{
		if( c_styleId == 0 )
		{
			c_error = "Please provide a style ID for meeting three out codes.";
			return;
		}
		if( c_file != null )
		{
			try {
				//Get stream from uploaded file
				InputStream l_istream = c_file.getInputStream();

				try {
					//Load derby database driver
					Class.forName("org.apache.derby.jdbc.ClientDriver").newInstance();
					//Create connection to database.  Create database if it doesn't exist.
					Connection l_conn = DAOFactory.getInstance().getConnection();

					//Create SQL statement object
					Statement l_query = l_conn.createStatement();
					
					//Test to see if the table exists, create it if it doesn't
					/* Now, we just try to select something from the table and if an error is thrown
					 * that contains "does not exist" then we try and create it.  Could be done
					 * better with T-SQL, doesn't handle the case where the table exists but 
					 * doesn't have the columns we are expecting.
					 */
					try
					{
						l_query.execute("SELECT COUNT(*) FROM ContestResults");
					}
					catch( SQLException e )
					{
						if( e.getMessage().contains("does not exist") )
						{
							l_query.execute("CREATE TABLE ContestResults ( ballotstyle integer, serial integer, question integer, symbol integer, code varchar(10) )");
						}
					}


					//Use prepared statement for queries with parameters
					PreparedStatement l_sqlStatement = l_conn.prepareStatement("INSERT INTO ContestResults VALUES (?, ?, ?, ?, ?)");
					PreparedStatement l_existsQuery = l_conn.prepareStatement("SELECT * FROM ContestResults WHERE serial=? AND ballotstyle=?");
					
					//Create documentbuilder and parse uploaded file
					DocumentBuilderFactory l_factory = DocumentBuilderFactory.newInstance();
					DocumentBuilder l_builder = l_factory.newDocumentBuilder();
					Document l_doc = l_builder.parse(l_istream);
					
					//Get all <ballot> elements
					NodeList l_nodes = l_doc.getElementsByTagName("ballot");
					for(int x = 0; x < l_nodes.getLength(); x++ )
					{
						
						//Read serial from ballot element
						Node l_node = l_nodes.item(x);
						//Ignore if not a ballot element (like #TEXT)
						if( !l_node.getNodeName().equals("ballot") )
							continue;
						
						int l_serial;
						int l_styleId;
						String l_serialString = l_node.getAttributes().getNamedItem("webSerial").getNodeValue();
						if( l_serialString.contains("-") )
						{
							String[] l_splits = l_serialString.split("-");
							l_serial = Integer.parseInt(l_splits[1]);
							l_styleId = Integer.parseInt(l_splits[0]);
						}
						else
						{
							l_serial = Integer.parseInt(l_serialString);
							l_styleId = c_styleId;
						}
						
						//Check to see if this ID is already in the database
						l_existsQuery.setInt(1, l_serial);
						l_existsQuery.setInt(2, c_styleId);
						if( l_existsQuery.executeQuery().next() )
						{
							c_error = "Some elements were already in the database and were ignored.";
							continue;
						}
						NodeList l_questionNodes = l_node.getChildNodes();
					
						//Loop over all <question> nodes
						//TODO: Add code here later if there can be more than one question
						for( int y = 0; y < l_questionNodes.getLength(); y++ )
						{
							//Ignore if not a question element (like #TEXT)
							if( !l_questionNodes.item(y).getNodeName().equals("question") )
								continue;
							
							int l_question = Integer.parseInt(l_questionNodes.item(y).getAttributes().getNamedItem("id").getNodeValue());
							
							NodeList l_symbolNodes = l_questionNodes.item(y).getChildNodes();
							
							int l_id = 1;
							//Loop over all <symbol> nodes
							for( int z = 0; z < l_symbolNodes.getLength(); z++ )
							{
								//Ignore if not a symbol element (like #TEXT)
								if( !l_symbolNodes.item(z).getNodeName().equals("symbol") )
									continue;
								
								//Read node attributes to get id and code
								NamedNodeMap l_symbolAttributes = l_symbolNodes.item(z).getAttributes();
								String l_code = l_symbolAttributes.getNamedItem("code").getNodeValue();

								//Set SQL parameters and add to batch
								l_sqlStatement.setInt(1, l_styleId);
								l_sqlStatement.setInt(2, l_serial);
								l_sqlStatement.setInt(3, l_question);
								l_sqlStatement.setInt(4, l_id);
								l_sqlStatement.setString(5, l_code);
								l_sqlStatement.addBatch();
								
								l_id++;
							}
						}
					}
					
					l_query.close();
					l_sqlStatement.executeBatch();
					
					l_sqlStatement.close();
					l_conn.close();
					c_result = "Codes added successfully";
					
				} catch (SQLException e) {
					//c_error = "Could not execute SQL: " + e.getMessage();
					while( e != null )
					{
						c_error += e.getMessage();
						e = e.getNextException();
					}
				} catch (InstantiationException e) {
					c_error = "Could not load derby driver: instantiation exception";
				} catch (IllegalAccessException e) {
					c_error = "Could not load derby driver: illegal access exception";
				} catch (ClassNotFoundException e) {
					c_error = "Could not load derby driver: class not found exception";
				} catch (ParserConfigurationException e) {
					c_error = "Could not load parser configuration";
				} catch (SAXException e) {
					c_error = "Could not parse XML file: " + e.getMessage();
				}

				l_istream.close();
			} catch (IOException e) {
				c_error = e.getMessage();
			}

		}
	}
	
	@SuppressWarnings("unchecked")
	private void parseChoices(boolean p_useWriteIns)
	{
		ScannerConfig l_config = GetConfig();
		
		if( l_config == null )
			return;
		
		try
		{
			TreeMap<Integer, Vector<ContestChoice>> l_choices = null;
			
			File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
			//File l_contestFile = new File(l_docsDir, "ContestChoices.xml");
			InputStream l_input = c_file.getInputStream();// new FileInputStream(l_contestFile);
			
			BufferedWriter l_writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(new File(l_docsDir, p_useWriteIns ? "Results.txt" : "ResultsRaw.txt"))));
			
			XMLDecoder l_dec = new XMLDecoder(l_input);
			Object l_decodedObject = l_dec.readObject();
			
			if( l_decodedObject instanceof TreeMap )
				l_choices = (TreeMap<Integer, Vector<ContestChoice>>)l_decodedObject;
			
			if( l_choices == null )
				throw new IOException();
			
			for( Contest l_contest : l_config.getContests() )
			{ 
				if( !l_choices.containsKey(l_contest.getId()) )
					continue;
				
				TallyMethod l_tally = l_contest.getTallyMethod();
				ContestResult l_res = l_tally.tally(l_contest, l_choices.get(l_contest.getId()));
				l_writer.write("<h3 style='color: olive;'>Contest " + (l_contest.getId() + 1) + ": " + l_contest.getContestName() + "</h3>");
				l_writer.write(l_res.getHtmlResults());
			}
			l_writer.close();
		}
		catch(IOException e)
		{
			c_error += "Could not open scanner config file. Please make sure that it has been uploaded.\n";
			return;
		}
	}
	
	private void parseResults()
	{
		try {
			File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
			if( !l_docsDir.exists() )
			{
				throw new FileNotFoundException("Docs folder could not be found");
			}
			BufferedWriter l_writer = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(new File(l_docsDir, "Results.txt"))));
			
			//Get stream from uploaded file
			InputStream l_istream = c_file.getInputStream();
			
			//Create documentbuilder and parse uploaded file
			DocumentBuilderFactory l_factory = DocumentBuilderFactory.newInstance();
			DocumentBuilder l_builder = l_factory.newDocumentBuilder();
			Document l_doc = l_builder.parse(l_istream);
			
			NodeList l_partitions = l_doc.getElementsByTagName("partition");
			Vector<Contest> l_contests = GetContests();
			if( l_contests == null ) return;
			Vector<Vector<Ballot>> l_ballots = GetData(l_partitions, l_contests);
		
			for( int x = 0; x < l_contests.size(); x++ )
			{
				TallyMethod l_tally = l_contests.get(x).getMethod();
				/*ContestResult l_res = l_tally.tally(l_contests.get(x), l_ballots.get(x));
				l_writer.write("<h3 style='color: olive;'>Contest " + (l_contests.get(x).getId() + 1) + ": " + l_contests.get(x).getContestName() + "</h3>");
				l_writer.write(l_res.getHtmlResults());*/
			}
			
			l_writer.close();
			
			c_result += "Results calculated successfully.";
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		finally
		{	}
		
	}
	
	private ScannerConfig GetConfig()
	{
		File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
		File l_configFile = new File(l_docsDir, "ScannerConfig.xml");
		System.out.println("Looking for scanner config at " + l_configFile.getPath());
		
		if( !l_configFile.exists() )
		{
			c_error = "Scanner config could not be found, please make sure it has been uploaded.";
			return null;
		}
		
		try
		{
			FileInputStream l_input = new FileInputStream(l_configFile);
			
			XMLDecoder l_dec = new XMLDecoder(l_input);
			Object l_decodedObject = l_dec.readObject();
			
			if( !(l_decodedObject instanceof ScannerConfig) )
			{
				c_error = "Unexpected scanner config format, could not load correctly.";
				return null;
			}
			
			if( l_decodedObject == null )
			{
				c_error = "Could not load scanner config.";
				return null;
			}
			
			return (ScannerConfig)l_decodedObject;
		}
		catch(IOException ex)
		{
			c_error = "Error reading scanner config.";
			return null;
		}
		
	}
	
	@SuppressWarnings("unchecked")
	private Vector<Contest> GetContests()
	{
		Vector<Contest> l_contests = null;//new Vector<Contest>();
		try
		{
			File l_docsDir = new File(c_ctx.getServletContext().getRealPath("/docs/"));
			File l_contestFile = new File(l_docsDir, "ContestInformation.xml");
			FileInputStream l_input = new FileInputStream(l_contestFile);
			
			XMLDecoder l_dec = new XMLDecoder(l_input);
			Object l_decodedObject = l_dec.readObject();
			
			if( l_decodedObject instanceof Vector )
				l_contests = (Vector<Contest>)l_decodedObject;
			
			if( l_contests == null )
				throw new IOException();
		}
		catch(IOException e)
		{
			c_error += "Could not open contest information file. Please make sure that it has been uploaded.\n";
			return null;
		}
		
		/*Contest l_contestOne = new Contest();
		l_contestOne.setId(0);
		l_contestOne.setContestName("Favorite Tree");
		Vector<Contestant> l_contestantsOne = new Vector<Contestant>();
		l_contestantsOne.add(new Contestant(0, "Cherry"));
		l_contestantsOne.add(new Contestant(1, "Elm"));
		l_contestantsOne.add(new Contestant(2, "Maple"));
		l_contestantsOne.add(new Contestant(3, "Oak"));
		l_contestantsOne.add(new Contestant(4, "Write-in"));
		l_contestOne.setContestants(l_contestantsOne);
		l_contestOne.setMethod(new InstantRunoffTally());
		
		Contest l_contestTwo = new Contest();
		l_contestTwo.setId(0);
		l_contestTwo.setContestName("Favorite Animal");
		Vector<Contestant> l_contestantsTwo = new Vector<Contestant>();
		l_contestantsTwo.add(new Contestant(0, "Owl"));
		l_contestantsTwo.add(new Contestant(1, "Rabbit"));
		l_contestantsTwo.add(new Contestant(2, "Squirrel"));
		l_contestantsTwo.add(new Contestant(3, "Write-in"));
		l_contestTwo.setContestants(l_contestantsTwo);
		l_contestTwo.setMethod(new InstantRunoffTally());
		
		Contest l_contestThree = new Contest();
		l_contestThree.setId(0);
		l_contestThree.setContestName("Number of Trees");
		Vector<Contestant> l_contestantsThree = new Vector<Contestant>();
		l_contestantsThree.add(new Contestant(0, "0"));
		l_contestantsThree.add(new Contestant(1, "1-2"));
		l_contestantsThree.add(new Contestant(2, "3-5"));
		l_contestantsThree.add(new Contestant(3, "5-10"));
		l_contestantsThree.add(new Contestant(4, "10+"));
		l_contestThree.setContestants(l_contestantsThree);
		l_contestThree.setMethod(new PluralityTally());
		
		Contest l_contestFour = new Contest();
		l_contestFour.setId(0);
		l_contestFour.setContestName("Less paper products");
		Vector<Contestant> l_contestantsFour = new Vector<Contestant>();
		l_contestantsFour.add(new Contestant(0, "Yes"));
		l_contestantsFour.add(new Contestant(1, "No"));
		l_contestFour.setContestants(l_contestantsFour);
		l_contestFour.setMethod(new PluralityTally());
		
		l_contests.add(l_contestOne);
		l_contests.add(l_contestTwo);
		l_contests.add(l_contestThree);
		l_contests.add(l_contestFour); */
		
		return l_contests;
	}
	
	private Vector<Vector<Ballot>> GetData(NodeList p_partitions, Vector<Contest> l_contests)
	{
		Vector<Vector<Ballot>> l_data = new Vector<Vector<Ballot>>();
		
		//System.err.println("Partitions: " + p_partitions.getLength());

		for( int x = 0; x < p_partitions.getLength(); x++ )
		{	
			
			Node l_contest = p_partitions.item(x);
			int l_contestId = Integer.parseInt(l_contest.getAttributes().getNamedItem("id").getNodeValue());
			
			Node l_results = null;
			for( int y = 0; y < l_contest.getChildNodes().getLength(); y++ )
			{
				Node l_child = l_contest.getChildNodes().item(y);
				if( l_child.getNodeName() == "results" )
					l_results = l_child;
			}
			
			NodeList l_rows = l_results.getChildNodes();
			
			//System.err.println("Rows: " + l_rows.getLength());

			int l_length = 0;
			
			Vector<Ballot> l_ballots = new Vector<Ballot>();
			
			for( int y = 0; y < l_rows.getLength(); y++ )
			{
				if( l_rows.item(y).getNodeName() == "row" )
				{
					Integer l_id = Integer.parseInt(l_rows.item(y).getAttributes().getNamedItem("id").getNodeValue());
					
					if( l_length == 0 )
					{
						l_length = l_rows.item(y).getAttributes().getNamedItem("r").getNodeValue().split(" ").length;
					}
				
					Map<Integer, Integer[][]> l_ballotData = new TreeMap<Integer, Integer[][]>();
					if(l_contests == null || l_contests.get(x) == null)
						continue;
					Integer[][] l_values = new Integer[l_contests.get(x).getContestants().size()][l_length];
					
					String[] l_splits = l_rows.item(y).getAttributes().getNamedItem("r").getNodeValue().split(" ");
					//System.err.println("Length: " + l_splits.length);
					//System.err.println(l_rows.item(y).getAttributes().getNamedItem("r").getNodeValue());
					
					for( int i = 0; i < l_values.length; i++ )
					{
						for( int k = 0; k < l_values[i].length; k++ )
						{
							l_values[i][k] = 0;
						}
					}
					
					for( int z = 0; z < l_splits.length; z++ )
					{
						int l_index = Integer.parseInt(l_splits[z]);
						if( l_index >= 0)
							l_values[Integer.parseInt(l_splits[z])][z] = 1;
					}
					
					l_ballotData.put(l_contestId, l_values);
					System.err.println("Adding ballot with Contest ID: " + l_contestId);
					
					l_ballots.add(new Ballot(l_id, 0, l_ballotData));
				}
			}
			
			l_data.add(l_ballots);
		}
		return l_data;
	}
	
	class ZipThread extends Thread
	{
		File c_dir;
		
		public ZipThread(File p_dir)
		{
			c_dir = p_dir;
		}
		
		public void run()
		{
			try
			{
				File l_zipFile = new File(c_dir, ".ElectionFiles.zip");
				FileOutputStream l_fo = new FileOutputStream(l_zipFile);
				ZipOutputStream l_zipOutput = new ZipOutputStream(l_fo);
		
				File[] l_xmlFiles = c_dir.listFiles(new XmlFileFilter());
				
				for(File l_newFile : l_xmlFiles )
				{
					l_zipOutput.putNextEntry(new ZipEntry(l_newFile.getName()));
					FileInputStream l_fi = new FileInputStream(l_newFile);
					byte[] l_bytes = new byte[1024];
					int l_read;
				
					while(-1 != (l_read = l_fi.read(l_bytes)) )
					{
						l_zipOutput.write(l_bytes, 0, l_read);
					}
					
					l_zipOutput.flush();
				}
				
				l_zipOutput.close();
				
				l_zipFile.renameTo(new File(c_dir, "ElectionFiles.zip"));
			}
			catch(IOException e)
			{
				System.err.println(e.getStackTrace());
			}
		}

	}
	
	class XmlFileFilter implements FilenameFilter
	{
		public boolean accept(File dir, String name) {
			return name.contains(".xml");
		}
		
	}

}