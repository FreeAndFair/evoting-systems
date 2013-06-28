/*
 * JML specification Copyright 2004 SoS Group, University of Nijmegen
 */

package sos.koa;

/**
 * Some static helper methods for dealing with hexadecimal notation.
 *
 * @version $Id: Hex.java,v 1.2 2004/05/04 19:51:52 martijno Exp $
 *
 * @author Martijn Oostdijk (martijno@cs.kun.nl)
 */
public class Hex {

   /**
    * This private constructor makes it impossible to create
    * instances of this class.
    */
   private Hex() {
   }

   /**
    * Converts the byte <code>n</code> to capitalized hexadecimal text.
    *
    * @param n The byte to convert.
    *
    * @return Capitalized hexadecimal text representation of
    *    <code>n</code>.
    */
   public static String byteToHexString(int n) {
      byte[] text = { (byte)(n & 0x000000FF) };
      return bytesToHexString(text);
   }

   /**
    * Converts the short <code>n</code> to capitalized hexadecimal text.
    *
    * @param n The short to convert.
    *
    * @return Capitalized hexadecimal text representation of
    *    <code>n</code>.
    */
   public static String shortToHexString(int n) {
      byte[] text = { (byte)((n & 0x0000FF00) >> 8),
                      (byte)(n & 0x000000FF) };
      return bytesToHexString(text);
   }

   /**
    * Converts the integer <code>n</code> to capitalized hexadecimal text.
    *
    * @param n The integer to convert.
    *
    * @return Capitalized hexadecimal text representation of
    *    <code>n</code>.
    */
   public static String intToHexString(int n) {
      byte[] text = { (byte)((n & 0xFF000000) >> 24),
                      (byte)((n & 0x00FF0000) >> 16),
                      (byte)((n & 0x0000FF00) >> 8),
                      (byte)(n & 0x000000FF) };
      return bytesToHexString(text);
   }

   /**
    * Converts a byte array to capitalized hexadecimal text.
    *
    * @param text The byte array to convert.
    *
    * @return Capitalized hexadecimal text representation of
    *    <code>text</code>.
    */
   public static String bytesToHexString(byte[] text) {
      return bytesToHexString(text,0,text.length);
   }

   /**
    * Converts part of a byte array to capitalized hexadecimal text.
    * Conversion starts at index <code>offset</code> until (excluding)
    * index <code>offset+length</code>.
    *
    * @param text The byte array to convert.
    * @param offset Where to start.
    * @param length How many bytes to convert.
    *
    * @return Capitalized hexadecimal text representation of
    *    <code>text</code>.
    */
   public static String bytesToHexString(byte[] text,
                                          int offset,
                                          int length) {
      String result = "";
      for (int i=0; i<length; i++) {
         int b = (text[offset+i] & 0x000000FF);
         if (b < 0x10) {
            result += "0"+Integer.toHexString(b);
         } else {
            result += Integer.toHexString(b);
         }
      }
      return result.toUpperCase();
   }

   public static short hexStringToShort(String text)
   throws NumberFormatException {
      byte[] bytes = hexStringToBytes(text);
      if (bytes.length != 2) {
         throw new NumberFormatException();
      }
      return (short)(((bytes[0] & 0xFF) << 8) | (bytes[1] & 0xFF));
   }

   /**
    * Converts the hexadecimal string in <code>text</code> to
    * a byte array. If <code>text</code> has an odd number of
    * characters, a <code>0</code> is inserted at the beginning.
    *
    * @param text The string to convert.
    *
    * @return The byte array representation of the hexadecimal string
    *    in <code>text</code>.
    */
   public static byte[] hexStringToBytes(String text)
   throws NumberFormatException {
      if (text==null) {
         return null;
      }
      final String hexchars = "0123456789abcdefABCDEF";
      StringBuffer hextext = new StringBuffer();
      for (int i=0; i < text.length(); i++) {
         char c = text.charAt(i);
         if (Character.isWhitespace(c)) {
            continue;
         } else if (hexchars.indexOf(c) < 0) {
            throw new NumberFormatException();
         } else {
            hextext.append(c);
         }
      }
      if (hextext.length() % 2 != 0) {
         hextext.insert(0,"0");
      }
      byte[] result = new byte[hextext.length()/2];
      for (int i = 0; i < hextext.length(); i+=2) {
         int hi = hexCharToInt(hextext.charAt(i));
         int lo = hexCharToInt(hextext.charAt(i+1));
         result[i/2] = (byte)(((hi & 0x000000FF) << 4)|(lo & 0x000000FF));
      }
      return result;
   }

   /**
    * Interprets the character <code>c</code> as hexadecimal
    * digit.
    *
    * @param c A character from
    *    <code>0,1,2,3,4,5,6,7,8,9,A,B,C,D,E,F</code>.
    *
    * @return The decimal-hexadecimal digit interpretation of
    *    <code>c</code>.
    */
   private static int hexCharToInt(char c)
   throws NumberFormatException {
      switch (c) {
         case '0': return 0;
         case '1': return 1;
         case '2': return 2;
         case '3': return 3;
         case '4': return 4;
         case '5': return 5;
         case '6': return 6;
         case '7': return 7;
         case '8': return 8;
         case '9': return 9;
         case 'a':
         case 'A': return 10;
         case 'b':
         case 'B': return 11;
         case 'c':
         case 'C': return 12;
         case 'd':
         case 'D': return 13;
         case 'e':
         case 'E': return 14;
         case 'f':
         case 'F': return 15;
         default: throw new NumberFormatException();
      }
   }
}

