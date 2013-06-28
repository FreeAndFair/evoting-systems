package uk.ac.surrey.pav.common;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;

/**
 * Used to convert to and from Hex
 * @author David
 *
 */
public class HexConstructor {

	/**
	 * Convert a byte array to a hex String
	 * 
	 * Provided by James Heather.
	 * 
	 * @param repair Byte array to turn into hex
	 * @return Hex string of the byte
	 */
	public static String byteArrayToHexString(byte repair[]) {

		String answer = "";
        for (int i=0; i<repair.length; i++) {

            answer += Integer.toHexString(0x0100 + (repair[i] & 0x00FF)).substring(1);

        }
        return answer;

	}
	
	/*public static String byteArrayToHexString(byte repair[]) {
		
		int length = repair.length * 2;
		StringBuffer padding = new StringBuffer();
		for(int x=0; x<length*2; x++) {
			padding.append(00);
		}
		String tempResult = padding + byteArrayToHexStringWithLeadingZeros(repair);
		return tempResult.substring(tempResult.length() - length, tempResult.length());
		
	}*/
	
	/**
	 * Converts a hex String to a byte array
	 * 
	 * Provided by James Heather
	 * 
	 * @param hex String hex
	 * @return Byte[] conversion of the hex input
	 */
	public static byte[] hexStringToByteArray(String hex) {

		byte[] packet = new byte[hex.length()/2]; 
		for (int j=0; j<packet.length; j++) {

        	packet[j] = (byte)Integer.parseInt(hex.substring(j*2,(j+1)*2), 16);

        }
		return packet;

	}
	
	/**
	 * Takes an object, serialises it and converts it to hex
	 * 
	 * @param object Object to serialise and turn into hex
	 * @return Hex string of the object serialisation
	 */
	public static String serializeIntoHex(Object object) {
		
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		ObjectOutputStream oout;
		try {
			
			oout = new ObjectOutputStream(baos);
			oout.writeObject(object);
			oout.close();
			byte[] buf = baos.toByteArray();
			return byteArrayToHexString(buf);
		
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}

	}
}
