

import java.io.*;
import java.math.*;

import com.onionnetworks.fec.FECCode;
import com.onionnetworks.fec.FECCodeFactory;
import com.onionnetworks.util.Buffer;


/**
 * @author James
 *
 */
public class BallotForms2Latex {
	
	/**
     * This is a receipt for a correctly posted vote
     */
    public static final int CORRECTLY_POSTED_RECEIPT = 31;
    
    /**
     * This is a receipt for an audit request
     */
    public static final int AUDIT_RECEIPT = 32;
    
    /**
     * This is a ballot form that is going to be printed
     */
    public static final int BALLOT_FORM_TO_BE_PRINTED = 30;
    
    /**
     * This is a remote ballot form to be printed
     */
    public static final int REMOTE_BALLOT_FORM_TO_BE_PRINTED = 33;
    
    /**
     * The poster is not a valid booth
     */
    public static final int ERROR_NOT_A_BOOTH = 41;
    
    /**
     * There was a problem with the database on the web bulletin board
     */
    public static final int ERROR_DATABASE_PROBLEM = 42;
    
    /**
     * The ballot form was invalid or did not correspond to the ballot form in the database
     */
    public static final int ERROR_INVALID_BALLOT_FORM = 43;
    
    /**
     * There was a different internal bulletin board problem
     */
    public static final int ERROR_INTERNAL_BULLETIN_BOARD_PROBLEM = 44;
    
    /**
     * A teller was down when an audit was attempted
     */
    public static final int ERROR_TELLER_DOWN = 45;
    
    /**
     * The ballot form has already been used
     */
    public static final int ERROR_BALLOT_FORM_USED = 46;
    
    /**
     * The hash check failed
     */
    public static final int ERROR_INVALID_HASH = 47;
	
	/**
	 * The vote didn't make sense (e.g., "13-") 
	 */
	public static final int ERROR_VOTE_MALFORMED = 48;
	
	public static final int ERROR_SCANNING_PROBLEM = 49;
		
	public static final int ERROR_NO_INPUT = 98;
	
	public static final int ERROR_LATEXING_PROBLEM = 99;
	
	//k = number of source packets to encode
    //n = number of packets to encode to
    public static int BARCODE_DATA_LINES = 44;
    public static int BARCODE_TOTAL_LINES = 64;
    public static int BARCODE_BYTES_PER_LINE = 3;

    public static String addFEC(String shorthex) {
        
        byte[] source = new byte[BARCODE_DATA_LINES*BARCODE_BYTES_PER_LINE]; 
        for (int j=0; j<BARCODE_DATA_LINES*BARCODE_BYTES_PER_LINE; j++) {
        	Integer byteint = Integer.parseInt(shorthex.substring(j*2,(j+1)*2),16);
        	source[j] = byteint.byteValue();
        }

        //NOTE:
        //The source needs to split into k*packetsize sections
        //So if your file is not of the write size you need to split it into
        //groups.  The final group may be less than k*packetsize, in which case
        //you must pad it until you read k*packetsize.  And send the length of the
        //file so that you know where to cut it once decoded.
                 
        byte[] repair = new byte[BARCODE_TOTAL_LINES*BARCODE_BYTES_PER_LINE]; //this will hold the encoded file
        
        //These buffers allow us to put our data in them
        //they reference a packet length of the file (or at least will once
        //we fill them)
        Buffer[] sourceBuffer = new Buffer[BARCODE_DATA_LINES];
        Buffer[] repairBuffer = new Buffer[BARCODE_TOTAL_LINES];
        
        for( int i = 0; i < sourceBuffer.length; i++ )
            sourceBuffer[i] = new Buffer( source, i*BARCODE_BYTES_PER_LINE, BARCODE_BYTES_PER_LINE );
            
        for( int i = 0; i < repairBuffer.length; i++ )
            repairBuffer[i] = new Buffer( repair, i*BARCODE_BYTES_PER_LINE, BARCODE_BYTES_PER_LINE );
        
        //When sending the data you must identify what its index was.
        //Will be shown and explained later
        int[] repairIndex = new int[BARCODE_TOTAL_LINES];
    
        for( int i = 0; i < repairIndex.length; i++ )
            repairIndex[i] = i;
        
        //create our fec code
        FECCode fec = FECCodeFactory.getDefault().createFECCode(BARCODE_DATA_LINES,BARCODE_TOTAL_LINES);
        
        //encode the data
        fec.encode( sourceBuffer, repairBuffer, repairIndex );
        //encoded data is now contained in the repairBuffer/repair byte array
      
        
        String answer = "";
        
        for (int i=0; i<repair.length; i++) {
        	answer += Integer.toHexString(0x0100 + (repair[i] & 0x00FF)).substring(1);
        }
        
        return answer;
    }

    public static String removeFEC(String[] lines, int[] index) {

    	//We only need to store k, packets received
        //Don't forget we need the index value for each packet too
        Buffer[] receiverBuffer = new Buffer[BARCODE_DATA_LINES];

        //this will store the received packets to be decoded
        byte[] received = new byte[BARCODE_DATA_LINES*BARCODE_BYTES_PER_LINE];
        
        for( int i = 0; i < BARCODE_DATA_LINES; i++ ) {
            byte[] packet = new byte[BARCODE_BYTES_PER_LINE]; 
            for (int j=0; j<BARCODE_BYTES_PER_LINE; j++) {
            	Integer byteint = Integer.parseInt(lines[i].substring(j*2,(j+1)*2),16);
            	packet[j] = byteint.byteValue();
            }
            System.arraycopy( packet, 0, received, i*BARCODE_BYTES_PER_LINE, packet.length);
        }
        
        //create our Buffers for the encoded data
        for( int i = 0; i < BARCODE_DATA_LINES; i++ )
            receiverBuffer[i] = new Buffer( received, i*BARCODE_BYTES_PER_LINE, BARCODE_BYTES_PER_LINE );
        
        //create our fec code
        FECCode fec = FECCodeFactory.getDefault().createFECCode(BARCODE_DATA_LINES,BARCODE_TOTAL_LINES);

        //finally we can decode
        fec.decode(receiverBuffer, index);
        
        String answer = "";
        
        for (int i=0; i<received.length; i++) {
        	answer += Integer.toHexString(0x0100 + (received[i] & 0x00FF)).substring(1);
        }
       
        return answer;       
    }
                
    private static String hashPrettyPrint(String hash) {
		BigInteger h = new BigInteger("00"+hash,16);
		String hashString = h.toString(32);
		while (hashString.length()<26)
			hashString = "0"+hashString;
		
		String hashPrettyString =
			hashString.substring(0,5) + "-" + hashString.substring(5,10) + "-" + hashString.substring(10,13) + "\\\\" + 
			hashString.substring(13,18) + "-" + hashString.substring(18,23) + "-" + hashString.substring(23,26); 
		
		return hashPrettyString;
	}
	
/*	private static String addEDAC(String signedHash) {
		String s = signedHash;

		for (int i=0; 2*i<signedHash.length(); i++) {
			s+="a";
		}
		return s;
	}
*/
    
	public static String header = "\\documentclass[a4paper]{article}\n\n\\usepackage%s{pav} \\usepackage{pav-vocomp}\n\\begin{document}\n\n";
	
	public static String footer = "\\end{document}\n";
	
/*	public static String[] racetitles =
		{"\\prestitleshort", "\\sportstitleshort", "\\soctitleshort", "\\edutitleshort",
		 "\\weltitleshort", "\\nustitleshort", "\\ftradetitleshort"};
*/
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
//		try{
//		BufferedReader in = new BufferedReader(new FileReader("c:\\users\\james\\Documents\\tex\\pav\\test-ballot-forms.csv"));
		
		String csvline;
		String[] tokens;
		String dvips = "[old-dvips]";
		Boolean found = false;

		if ((args.length>=1) && (args[0].equals("shrink"))) {
			dvips = "";
		}
		
		System.out.printf(header, dvips);
		
		try {
			while ((csvline = in.readLine()) !=null && csvline.length()>0) {
				
				found = true;
				
				tokens = csvline.split(",");
				
				String serialhex = Integer.toHexString(Integer.decode(tokens[1]));
				while (serialhex.length()<8)
					serialhex = "0"+serialhex;
				String fechash = addFEC(tokens[4]+serialhex);
				
				int numballots = Integer.decode(tokens[5]);
				
				int balnum=6;
				String balnumstr = "";
				for (int i=0; i<numballots; i++) {
					balnumstr += "{" + tokens[balnum+i] + "}";
				}
				
				switch (Integer.decode(tokens[0])) {
				case BALLOT_FORM_TO_BE_PRINTED: { 
					System.out.printf("\\begin{ballot2007}{%06d}{%s}{%s}\n  \\ballotnums%s\n\\end{ballot2007}\n\n",
							Integer.decode(tokens[1]), fechash, hashPrettyPrint(tokens[3]),
							balnumstr);
					break;
				}
				case CORRECTLY_POSTED_RECEIPT: {
					System.out.printf("\\begin{receipt2007}{%06d}{%s}{%s}\n  \\receiptnums%s\n\\end{receipt2007}\n\n",
							Integer.decode(tokens[1]), fechash, hashPrettyPrint(tokens[3]),
							balnumstr);
					break;
				}
				case AUDIT_RECEIPT: {
					System.out.printf("\\begin{audit2007}{%06d}{%s}{%s}\n  \\auditnums%s\n\\end{audit2007}\n\n",
							Integer.decode(tokens[1]), fechash, hashPrettyPrint(tokens[3]),
							balnumstr);
					break;
				}
				case REMOTE_BALLOT_FORM_TO_BE_PRINTED: {
					System.out.printf("\\begin{remote2007}{%06d}{%s}{%s}\n  \\remotenums%s\n\\end{remote2007}\n\n",
							Integer.decode(tokens[1]), fechash, hashPrettyPrint(tokens[3]),
							balnumstr);
					break;
				}
				case ERROR_VOTE_MALFORMED: {
					String cancelstring = "";
					String hintstring = "";
					for (int i=0; i<numballots; i++) {
						try {
							hintstring = tokens[numballots+6+i];
						} catch (ArrayIndexOutOfBoundsException e) {
							hintstring = "";
						}
						if (!hintstring.isEmpty())
							cancelstring += "  \\item[Race "+(i+1)+":] "+hintstring+"\n";
					}
					if (cancelstring.isEmpty())
						cancelstring = "  \\item ~";
					System.out.printf("\\begin{cancel2007}{%06d}{%s}{%s}{%s}\n  \\cancelnums%s\n\\end{cancel2007}\n\n",
							Integer.decode(tokens[1]), fechash, hashPrettyPrint(tokens[3]), cancelstring,
							balnumstr);
					break;
				}
				case ERROR_BALLOT_FORM_USED: {
					System.out.println("\\begin{usedproblem}\\end{usedproblem}\n");
					break;
				}
				case ERROR_SCANNING_PROBLEM: {
					System.out.println("\\begin{scanproblem}\\end{scanproblem}\n");
					break;
				}
				default: {
					System.out.printf("\\begin{submitproblem}{%s}\\end{submitproblem}\n\n", tokens[0]);
					break;				
				}
				}
			}		
		} catch (Exception e) {
			System.err.println("Unhandled exception: "+e);
			System.out.println("\\begin{submitproblem}{"+ERROR_LATEXING_PROBLEM+"}\\end{submitproblem}\n");
			System.out.println(footer);
			System.exit(1);
		}

		if (!found) {
			System.out.println("\\begin{submitproblem}{"+ERROR_NO_INPUT+"}\\end{submitproblem}\n");
			System.out.println(footer);
			System.exit(1);			
		}
		
		System.out.println(footer);
//		} catch (Exception e) {}
	}

}
