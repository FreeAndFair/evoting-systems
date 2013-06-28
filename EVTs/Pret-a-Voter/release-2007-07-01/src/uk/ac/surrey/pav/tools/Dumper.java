package uk.ac.surrey.pav.tools;

import java.io.FileOutputStream;
import java.io.PrintStream;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.Statement;

import uk.ac.surrey.pav.common.HexConstructor;

public class Dumper {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		try {
			
			//Open database connection
			Class.forName ("com.mysql.jdbc.Driver");
			Connection connection = DriverManager.getConnection("jdbc:mysql://localhost/pretavoter", "root", "root");
	
			//Open a file
			FileOutputStream fos;
			fos = new FileOutputStream("C:/ballotformserialhash.csv");
			PrintStream p = new PrintStream(fos);
			
			//Get the ballotFormPapers from database
			Statement statement = connection.createStatement(ResultSet.TYPE_SCROLL_INSENSITIVE, ResultSet.CONCUR_READ_ONLY);
			ResultSet rsBallotFormPapers = statement.executeQuery("SELECT ballotformpaper_id AS serial, ballotformpaper_hash AS hash FROM ballotformpapers");
			
			//For each ballotFormPaper...
			while(rsBallotFormPapers.next()) {

				//...output serial number and hash to file
				StringBuffer result = new StringBuffer();
				result.append(rsBallotFormPapers.getInt("serial"));
				result.append(",");
				result.append(HexConstructor.byteArrayToHexString(rsBallotFormPapers.getBytes("hash")));
				
				p.println(result);
				
			}
			
			//Close file
			p.close();
			
			//Close database connection
			connection.close();
			
		} catch (Exception e) {
			
			e.printStackTrace();
			
		}

	}

}
