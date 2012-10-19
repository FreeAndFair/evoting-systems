/*
 * @(#)RandomBallotStore.java.java
 *  
 * Copyright (C) 2008-2009 Scantegrity Project
 * 
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package org.scantegrity.common;

import java.beans.XMLDecoder;
import java.beans.XMLEncoder;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.SecureRandom;
import java.util.Vector;
import java.io.File;

/**
 * Stores ballot objects at a random location in a large file. The intent is to
 * provide some anonymity by destroying the order in which ballots have been
 * entered into the system. 
 * 
 * The approach is to randomly place ballots in the file with hashing.
 * When a collision occurs, it tries again. When a threshold is reached, it 
 * attempts to place the ballot ahead of or behind the most recent collision.
 * 
 * A table at the beginning of the file records where each entry is located.
 * Ballots also begin with the string BALLOT and the size of the file as a 64 
 * bit number. This redundancy is meant to be helpful in file recovery 
 * situations.
 * 
 * 
 * TODO:
 * 	- Block structure could/should be encapsulated in it's own class. That would
 * 	  make it a little easier to follow.
 *  - File table should be able to tell us all the blocks that comprise a file.
 *    Perhaps we should have an additional file table entry structure.
 *  - Part of the block structure should allow for a cryptographic checksum.
 *    This would mandate a mimimum size for all blocks(e.g. 4-16k, or so).
 *  - Encrypt the data - Link this with a TPM?
 *  
 * All these future directions are good, but we're just trying to get the random
 * storage functionality down at this point in time. 
 * 
 * NOTE: The c_size/c_dsize params in Block have to be handled carefully.
 * 
 * 
 * @author Richard Carback
 *
 */
public class RandomBallotStore
{
	private static String FILESTART = "RAF0";
	private static String INVALID_FORMAT = "Unrecognized File Format";
	private static String INVALID_SIZE = "Invalid file size parameter.";
	private static String INVALID_BLKSIZE = "Invalid block size parameter."; 
	private static String FILE_EXISTS = "File already exists.";
	private static String OOM = "Out of Memory!";
	private static String BLTSTART = "BALLOT";
	private static String NXTBLK = "NEXT";
	private static String PRVBLK = "PREV";
	private static String ENDBLK = "DONE";
	private static byte FREEBLK = 0;
	private static byte BLTBLK = 1;
	private static byte CNTBLK = -1;
	private String c_fname = "";
	private int c_scannerId = -1;
	private RandomAccessFile c_file = null;
	private byte c_btab[] = null;
	private int c_blksize = 0;
	private int c_size = 0; 
	private int c_numBlks = 0;
	private long c_fsize = 0;
	private MessageDigest c_digest = null;
	private SecureRandom c_csprng = null;
		
	/**
	 * Create a new RandomBallotStore Object.
	 * 
	 * @param p_fname
	 * @throws NoSuchAlgorithmException 
	 */
	public RandomBallotStore(int p_scannerId, int p_size, int p_blksize, String p_fname, MessageDigest p_hash, 
								SecureRandom p_csprng) throws NoSuchAlgorithmException
	{
		c_scannerId = p_scannerId;
		c_size = p_size; 
		c_blksize = p_blksize;
		c_fname = p_fname;
		
		if (p_hash == null)
		{
			c_digest = MessageDigest.getInstance("SHA-256");			
		}
		else
		{
			c_digest = p_hash;
		}
		
		if (p_csprng == null)
		{
			c_csprng = SecureRandom.getInstance("SHA1PRNG");
		}
		else
		{
			c_csprng = p_csprng;
		}
		//NOTE: this might be problematic, but probably not if it uses 
		// /dev/random - Need to check/be careful on this one. Date seeding (usually bad anyway)
		// will not work in this context.
		c_csprng.generateSeed(20); // 20*8 = 160 bits.
	}
	
	public int initializeStore()
	{
		File l_file = new File(c_fname);
		int l_i = 0;
		while (l_file.exists())
		{
			try
			{
				return open();
			}
			catch (IOException e_io)
			{
			}
			
			//Failure, move the file to a different name, or change our name...
			l_file = new File(c_fname + "-" + l_i);
			l_i++;
		}
		
		try 
		{
			create(c_size, c_blksize);
			return 0; 
		} 
		catch (IOException e_io) 
		{
			//Critical failure, unable to write.
			return -1; 
		}
		
	}
	
	/**
	 * Open and set up a pre-existing ballot file. If this function detects
	 * a problem it will throw an IOException with a string that explains the
	 * specific error.
	 * 
	 * @return the number of ballots found in the file.
	 * @throws IOException
	 */
	public int open() throws IOException
	{
		c_file = new RandomAccessFile(c_fname, "rwd");
		
		if (c_file.length() < 20) 
		{
			throw new FileNotFoundException();
		}
		
		//Verify File Type
		byte l_fstart[] = new byte[FILESTART.getBytes().length];
		c_file.read(l_fstart);
		String l_fstartstr = new String(l_fstart);
		if (!l_fstartstr.equals(FILESTART))
		{
			throw new IOException(INVALID_FORMAT);
		}
		//If valid, read the next long for the file size.
		c_fsize = c_file.readInt();
		if (c_fsize < 0)
		{
			throw new IOException(INVALID_SIZE);
		}
		//Read the blksize
		c_blksize = c_file.readInt();
		if (c_blksize % 2 != 0)
		{
			throw new IOException(INVALID_BLKSIZE);
		}
		//Read the scannerId
		c_scannerId = c_file.readInt();		
		//Read the scannerId
		c_numBlks = c_file.readInt();		
		c_btab = new byte[c_numBlks];
		int l_numBallots = 0;
		for (int i = 0; i < c_btab.length; i++)
		{
			c_btab[i] = c_file.readByte();
			if (c_btab[i] > 0) {
				l_numBallots++;
			}
		}
		
		/*
		System.out.println("File Size: " + c_fsize);
		System.out.println("Block Size: " + c_blksize);
		System.out.println("NumBlks: " + c_numBlks);
		*/
		
		return l_numBallots;
	}
	
	
	/**
	 * Using the size and blksize, create a new ballot file.
	 * 
	 * @param p_size
	 * @param p_blksize
	 * @return
	 * @throws IOException 
	 */
	public int create(long p_size, int p_blksize) throws IOException
	{
		c_file = new RandomAccessFile(c_fname, "rwd");
		if (c_file.length() != 0)
		{
			//throw new IOException(FILE_EXISTS);
		}
		
		//Calculate true file size
		int l_tabSize = getTabSize(p_size, p_blksize);
		long l_evenSize = (p_size - FILESTART.getBytes().length - 16 - l_tabSize)/p_blksize;
		l_evenSize *= p_blksize;
		l_evenSize += l_tabSize;
		l_evenSize += FILESTART.getBytes().length + 16;
		
		c_fsize = l_evenSize;
		c_blksize = p_blksize;
		c_btab = new byte[l_tabSize];
		c_numBlks = l_tabSize;
		
		int l_size = FILESTART.getBytes().length + 16 + l_tabSize + c_numBlks*c_blksize;
		
		c_file.setLength(l_size);
		c_file.write(FILESTART.getBytes());
		c_file.writeInt(l_size);
		c_file.writeInt(p_blksize);
		c_file.writeInt(c_scannerId);
		c_file.writeInt(c_numBlks);
		c_file.getFD().sync();
		
		/*
		System.out.println("Size: " + l_evenSize);
		System.out.println("blksize: " + c_blksize);
		System.out.println("table entries: " + c_numBlks);
		*/
		return 0;
	}
	
	public void addBallot(Ballot p_ballot) throws IOException
	{
		//Convert the ballot into a serialized or XML Serialized object
		ByteArrayOutputStream l_ballot = new ByteArrayOutputStream();
		XMLEncoder l_enc = new XMLEncoder(l_ballot);
		l_enc.writeObject(p_ballot);
		l_enc.close();
		
		byte l_arr[] = l_ballot.toByteArray();
		/*for (int l_i = 0; l_i < l_arr.length; l_i++)
		{
			//l_arr[l_i] = (byte)('A');
		}*/
		
		Vector<Block> l_blks = generateBlks(l_arr);
		
		//Remaining blocks
		//TODO: push this out elsewhere (doesn't need to be done on each insert)
		int l_numLeft = 0;
		for (int l_i = 0; l_i < c_numBlks; l_i++)
		{
			if (c_btab[l_i] == FREEBLK)
			{
				l_numLeft++;
			}
		}
		//Throw exception if we are out of room.
		if (l_blks.size() > l_numLeft) 
		{
			throw new IOException(OOM);
		}
		
		int l_prevPos = -1;
		int l_blkPos = -1;
		for (int l_i = 0; l_i < l_blks.size(); l_i++)
		{
			//hash each block to find it's position.
			int l_pos = getBlkLoc(l_blks.get(l_i).getData(), l_numLeft);
			l_numLeft--;
			
			//Find the correct free blk
			int l_countPos = 0;
			l_blkPos = 0;
			while (l_blkPos < c_numBlks)
			{
				//System.out.println(c_btab[l_blkPos] + ", " + l_blkPos + ", " + l_countPos);
				if (c_btab[l_blkPos] == FREEBLK)
				{
					if (l_countPos >= l_pos) break;
				 	else l_countPos++;	
				}
			
				l_blkPos++;
			}
						
			if (l_blkPos >= c_numBlks || c_btab[l_blkPos] != FREEBLK) 
			{
				throw new IOException(OOM);
			}
			
			//If a position is found, check to make sure it's actually all 0's
			//throw an IOException if it's not.
			/*
			if (!isPosEmpty(l_pos)) 
			{
				throw new IOException("Found used data in unused block!");
			}*/
			
			//Mark the table entry
			if (l_i == 0) c_btab[l_blkPos] = BLTBLK;
			else c_btab[l_blkPos] = CNTBLK;
			
			//If there is a previous block
			if (l_prevPos != -1)
			{
				l_blks.get(l_i).setPrev(l_prevPos);
				l_blks.get(l_i-1).setNext(l_blkPos);
				writeBlock(l_prevPos, l_blks.get(l_i-1).getBytes());
			}
			l_prevPos = l_blkPos;
		}
		
		//Write the last block
		writeBlock(l_blkPos, l_blks.lastElement().getBytes());
				
		//Force a Sync of the file w/ the disk.
		c_file.getFD().sync();
	}
	

	public Vector<Ballot> getBallots() throws IOException
	{
		Vector<Ballot> l_res = new Vector<Ballot>();
		//Read the table entries for ballots
		for (int l_i = 0; l_i < c_numBlks; l_i++)
		{
			if (c_btab[l_i] == BLTBLK)
			{
				//Read the ballot
				byte l_ballot[] = readFile(l_i);
				//convert each serialized ballot into a ballot object
				ByteArrayInputStream l_in = new ByteArrayInputStream(l_ballot);
				XMLDecoder l_bData = new XMLDecoder(l_in);
				Ballot l_b = null;
				try
				{
					 l_b = (Ballot) l_bData.readObject();
				} catch (Exception l_e)
				{
					//TODO
					//Ignore exceptions here, but report that there is
					//a problem
					l_b = null;
				}
				//Make sure the ballot object "makes sense"
				//TODO: Ballot object checker.
				
				//Add the ballot into the list
				if (l_b != null)
				{
					l_res.add(l_b);
				}
			}
		}
		
		return l_res;
	}
	
	public Vector<Integer> getBallotIds() throws IOException
	{
		Vector<Integer> l_res = new Vector<Integer>();
		Ballot l_tmp;

		for (int l_i = 0; l_i < c_numBlks; l_i++)
		{
			if (c_btab[l_i] == BLTBLK)
			{
				//Read the ballot
				byte l_ballot[] = readFile(l_i);
				//convert each serialized ballot into a ballot object
				ByteArrayInputStream l_in = new ByteArrayInputStream(l_ballot);
				XMLDecoder l_bData = new XMLDecoder(l_in);
				l_tmp = null;
				try
				{
					 l_tmp = (Ballot) l_bData.readObject();
				} catch (Exception l_e)
				{
					//TODO
					//Ignore exceptions here, but report that there is
					//a problem
					l_tmp = null;
				}
				//Make sure the ballot object "makes sense"
				//TODO: Ballot object checker.
				
				//Add the ballot into the list
				if (l_tmp != null)
				{
					l_res.add(l_tmp.getId());
				}
			}
		}	
		return l_res;
	}
	
	/**
	 * Read an entire file in to memory that begins at block p_start.
	 * 
	 * @param p_start the starting block.
	 * @return
	 * @throws IOException 
	 */
	private byte[] readFile(int p_start) throws IOException
	{
		byte[] l_res = null;
		Vector<byte[]> l_blks = new Vector<byte[]>();

		int l_nxt = p_start;		
		Block l_cur = new Block();
		l_cur.setBytes(getBlk(l_nxt), 0);
		l_blks.add(l_cur.getData());
		int l_size = l_cur.getData().length;
		while (l_cur.getType() != Block.TYPE_END)
		{
			l_nxt = l_cur.getNext();
			l_cur.setBytes(getBlk(l_nxt), 0);
			l_blks.add(l_cur.getData());
			l_size += l_cur.getData().length;
		}
		
		//Re-assemble the file
		l_res = new byte[l_size];
		byte l_tmp[] = null;
		int l_pos = 0;
		for (int l_i = 0; l_i < l_blks.size(); l_i++)
		{
			l_tmp = l_blks.get(l_i);
			System.arraycopy(l_tmp, 0, 
								l_res, l_pos, l_tmp.length);
			l_pos += l_tmp.length;
		}
		/*
		String x = new String(l_res);
		System.out.println(x);
		*/
		return l_res;
	}
	
	/**
	 * Read a block into memory.
	 * @param p_start
	 * @return
	 * @throws IOException 
	 */
	private byte[] getBlk(int p_blkId) throws IOException
	{
		byte l_res[] = new byte[c_blksize];
		long l_offset = FILESTART.getBytes().length + 16 + c_numBlks;

		//System.out.println("Reading Block: " + p_blkId);
		//System.out.println("Offset: " + (l_offset + p_blkId*c_blksize));
		//System.out.println(c_numBlks);
		//read the block		
		c_file.seek(l_offset+p_blkId*c_blksize);
		c_file.read(l_res);	
		
		//System.out.println("Block Data:");
		//System.out.println(new String(l_res));
		
		
		return l_res;
	}

	/**
	 * Close the file.
	 * 
	 * @throws IOException
	 */
	public void close() throws IOException
	{
		c_file.close();
	}
	
	private void writeBlock(int p_pos, byte[] p_blk) throws IOException
	{
		long l_offset = FILESTART.getBytes().length + 16;
		
		//System.out.println(l_offset+c_numBlks+p_pos*c_blksize);
		//System.out.println(c_numBlks);
		c_file.seek(l_offset+c_numBlks+p_pos*c_blksize);
		c_file.write(p_blk);
		
		//Write the table
		c_file.seek(l_offset+p_pos);
		c_file.writeByte(c_btab[p_pos]);
	}
	
	
	/**
	 * Calculates the size of the table needed to address all of the blocks in 
	 * the file.
	 * 
	 * TBD: This approximation could be more exact. There's no reason to use
	 * a whole block when a specific size is possible. 
	 * 
	 * Note, int should be safe here. I don't think we'll be addressing 
	 * more than 2 gigs of entries. 
	 *  
	 * @param p_fsize the File size.
	 * @param p_blksize the Block size.
	 * @return
	 */
	private int getTabSize(long p_fsize, long p_blksize)
	{
		//How many blks are possible?
		long l_numBlks = (p_fsize - FILESTART.length() - 16)/p_blksize;
		//How many will I need to lose for the table?
		long l_numLost = (long)Math.ceil((double)l_numBlks/(double)p_blksize);

		//System.out.println(l_numBlks + ", " + l_numLost);
		
		return (int)(l_numBlks-l_numLost);
	}
	
	
	/**
	 * Break ballot data up into blocks.
	 * 
	 * @param p_data The data to break up.
	 * @return an array of each block and it's relevant data.
	 * @throws IOException 
	 * @throws IOException
	 */
	private Vector<Block> generateBlks(byte[] p_data) throws IOException 
	{
		Vector<Block> l_blks;		
		l_blks = new Vector<Block>();
		
		int l_size = p_data.length;
		Block l_cur = new Block(Block.TYPE_START, c_blksize);
		//NOTE: IF block size varies, this algorithm will have to change!
		int l_dsize = l_cur.getData().length;
		int l_dpos = 0; // data block pointer
		while (l_dpos < l_size)
		{
			//Last block - Will what's left fit in the block?
			if (l_size-l_dpos <= l_dsize)
			{
				l_cur.setType(Block.TYPE_END);
				l_cur.write(p_data, l_dpos, l_size-l_dpos);
				l_dpos = l_size; //loop terminating condition				
			}
			else
			{
				//Normal block
				l_cur.write(p_data, l_dpos, l_dsize);
				l_dpos += l_dsize;
			}
			
			l_blks.add(l_cur);
			l_cur = new Block(Block.TYPE_CONT, c_blksize);
		}
		
		return l_blks;
	}
	
	
	/**
	 * Given an arbitrary blk of ballot data, produce an index location.
	 * 
	 * The number is produced by concatenation of the ballot data with 
	 * 20 bytes generated by a CSPRNG. The result is modded with the number
	 * of possible blks to return the location.  
	 * 
	 * 
	 * @param p_b the block of data to hash.
	 * @param p_range the # of blocks left.
	 * @return location in the 
	 */
	private int getBlkLoc(byte[] p_b, int p_range) 
	{
		if (p_range <= 0) return 0;
		byte l_rnum[] = new byte[20];
		c_csprng.nextBytes(l_rnum);
		c_digest.update(l_rnum);
		BigInteger l_bInt = (new BigInteger(c_digest.digest(p_b))).abs();
		l_bInt = l_bInt.mod(BigInteger.valueOf(p_range));	
		return l_bInt.intValue();
	}
	
	/**
	 * @return the scannerId
	 */
	public int getScannerId() {
		return c_scannerId;
	}

	/**
	 * @param p_scannerId the scannerId to set
	 */
	public void setScannerId(int p_scannerId) {
		c_scannerId = p_scannerId;
	}

	/**
	 * Encapsulated block structure. When we want to save a few bits, we can
	 * modify the functions here to react to different block types and be more
	 * smart about if there is a need to write previous and next pointers.
	 * 
	 * @author Richard Carback
	 *
	 */
	private class Block
	{
		private static final byte TYPE_START = 1; //Starting block
		private static final byte TYPE_CONT = 2; //Middle Block
		private static final byte TYPE_END = 3; //Ending Block
		
		private static final String c_start = "BLK";
		
		private byte c_type = -1;
		private int c_next = -1;
		private int c_prev = -1;
		private int c_size = 0;
		private int c_dsize = 0;
		private byte c_data[] = null;
		
		/**
		 * Creates an empty, invalid block object.
		 */
		public Block()
		{
			c_type = -1;
			c_size = -1;
			c_dsize = -1;
			c_next = -1;
			c_prev = -1;
			c_data = null;
		}
		
		/**
		 * Creates a block object of specified type and block size.
		 * 
		 * @param p_type type of block (start, continuing, end, etc). 
		 * @param p_size the size of block.
		 * @throws IOException 
		 */
		public Block(byte p_type, int p_size) throws IOException
		{
			setType(p_type);
			setSize(p_size);
			c_next = -1;
			c_prev = -1;
		}
		
		public byte[] getHeader() throws IOException
		{
			ByteArrayOutputStream l_b = new ByteArrayOutputStream();
			DataOutputStream l_out = new DataOutputStream(l_b);
			l_out.writeChars(c_start);
			l_out.write(c_type);
			l_out.writeInt(c_size);
			l_out.writeInt(c_prev);
			l_out.writeInt(c_next);
			
			return l_b.toByteArray();
		}
		
		public int getHeaderSize() throws IOException
		{
			return getHeader().length;
		}
				
		/**
		 * Generate and return the bytes contained in this block.
		 * 
		 * @return
		 * @throws IOException
		 */
		public byte[] getBytes() throws IOException
		{
			ByteArrayOutputStream l_b = new ByteArrayOutputStream();
			DataOutputStream l_out = new DataOutputStream(l_b);
			l_out.writeBytes(c_start);
			l_out.write(c_type);
			l_out.writeInt(c_dsize);			
			l_out.writeInt(c_prev);
			l_out.writeInt(c_next);
			//Write the block		
			/*
			System.out.print("Writing: ");
			for (int i=0; i < 30; i++) System.out.print((char)c_data[i]);
			System.out.println("");
			*/
			l_out.write(c_data);
			return l_b.toByteArray();
		}
		
		/**
		 * Parse the bytes as if they were generated by the getBytes function.
		 * This sets the object to contain the same data as what is represented
		 * in the byte stream.
		 * 
		 * @param p_block
		 * @throws IOException 
		 */
		public void setBytes(byte[] p_block, int p_off) throws IOException
		{
			ByteArrayInputStream l_b = new ByteArrayInputStream(p_block);
			DataInputStream l_in = new DataInputStream(l_b);
			
			//Read the block identifier.
			byte l_id[] = new byte[c_start.length()];
			l_in.read(l_id);
			String l_tmp = new String(l_id);
			
			if (!l_tmp.equals(c_start)) {
				throw new IOException("Unrecognized block");
			}
			
			c_type = l_in.readByte();
			c_dsize = l_in.readInt();
			c_size = c_dsize + getHeaderSize();
			c_prev = l_in.readInt();
			c_next = l_in.readInt();
			/*
			System.out.println("Type: " + c_type);
			System.out.println("Size: " + c_size);
			System.out.println("Prev: " + c_prev);
			System.out.println("Next: " + c_next);
			*/
			c_data = new byte[c_dsize];
			l_in.read(c_data, 0, c_dsize);
		}

		/**
		 * @param p_data
		 * @param p_off
		 * @param p_length
		 */
		public void write(byte[] p_data, int p_off, int p_length)
		{
			if (p_length > c_dsize)
			{
				p_length = c_dsize;
			}
			//Write the block		
			/*
			System.out.print("Writing: ");
			for (int i=0; i < 30; i++) System.out.print((char)p_data[i+p_off]);
			System.out.println("");
			*/
			c_dsize = p_length;
			System.arraycopy(p_data, p_off, c_data, 0, p_length);
		}
		

		/**
		 * Changes the size of this block.
		 * 
		 * @param p_size
		 * @throws IOException 
		 */
		public void setSize(int p_size) throws IOException
		{
			c_size = p_size;
			c_dsize = c_size - getHeaderSize();
			byte l_tmp[] = new byte[c_dsize];
			if (c_data != null)
			{
				System.arraycopy(c_data, 0, l_tmp, 0, c_data.length);
			}
			c_data = l_tmp;
		}		
		
		/**
		 * The size of this block object.
		 * @return -1 if the block is invalid.
		 */
		public int size()
		{
			return c_size;
		}
				
		/**
		 * Set what type of block object this is.
		 * 
		 * @param p_type
		 */
		public void setType(byte p_type)
		{
			c_type = p_type;
		}
		
		/**
		 * This blocks type. -1 is an invalid block.
		 * 
		 * @return
		 */
		public byte getType()
		{
			return c_type;
		}
		
		/**
		 * Location of previous block.
		 * 
		 * @return
		 */
		public int getPrev()
		{
			return c_prev;
		}
		
		public void setPrev(int p_prev)
		{
			c_prev = p_prev;
		}
		
		/**
		 * Location of th enext block.
		 * 
		 * @return
		 */
		public int getNext()
		{
			return c_next;
		}
		
		public void setNext(int p_next)
		{
			c_next = p_next;
		}
		
		
		/**
		 * Return the data segment of this block.
		 * 
		 * @return
		 */
		public byte[] getData()
		{
			return c_data;
		}
		
	}

	public String getLocation() {
		return c_fname;
	}
	
	
}
