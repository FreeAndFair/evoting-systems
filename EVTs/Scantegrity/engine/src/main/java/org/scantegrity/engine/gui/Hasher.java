package org.scantegrity.engine.gui;
import java.util.*;
import java.io.*;
import java.security.*;

public class Hasher extends Thread {
    public interface HashingProgressMonitor {
        public void updateHashingProgress( int current, int maximum );
        public void finishedHashing( Vector<byte[]> hashes, Vector<File> drives, long durationMS );
    }

    private Vector<File> drives;
    private Vector<HashingProgressMonitor> monitors = new Vector<HashingProgressMonitor>();
    private Vector<byte[]> hashes = new Vector<byte[]>();
    private static boolean cancelNow = false;
    
    public Hasher( Vector<File> driveVec )
    {
        drives = driveVec;
    }
    
    public void addMonitor( HashingProgressMonitor mon )
    {
        monitors.add( mon );
    }
    
    public Vector<byte[]> getHashes() 
    { 
        return hashes; 
    }
    
    // wild ass guess for image/drive size (bytes) when real size is unknown
    private final int GuessImageSize = 650000000;
    
    // Wild ass guess for boot sector size. (in bytes)
    private final int BootSectorSize = 10000000;
    
    // size of data blocks processed (in bytes)
    private final int BlockSize = 32768; 
    
    public void run()
    {
        long total = 0;
        int done, curProgress = 0;
        
        long duration = 0, start = Calendar.getInstance().getTimeInMillis();
        
        Vector<HasherThread> hashers = new Vector<HasherThread>();
        for (int i = 0; i < drives.size(); i++)
        {
            // Create each individual hasher thread and get them started
            HasherThread ht = new HasherThread( drives.get(i) );
            hashers.add( ht );
            ht.start();
            total += ht.getSizeToHash();
        }
        
        total = total/BlockSize;
        if ( total < 1 )
            total = 1;
        
        // Main loop
        do 
        {
            // Sleep for a while to let the workers do their thing
            try {
                if ( cancelNow )
                    Thread.sleep( 10 ); // sleep less time if we're canceling
                else
                    Thread.sleep( 100 );
            } catch ( InterruptedException ie ) { }
            
            curProgress = 0;
            done = 0;
            
            // Go through each worker and get their progress
            for (int i = 0;i < hashers.size(); i++)
            {
                HasherThread ht = hashers.get(i);
                
                curProgress += ht.getProgress();
                
                if ( !ht.isAlive() )
                    done++;
            }
            
            // sanity check, total should never be less than current position
            if ( total < curProgress )
                total = curProgress;
            
            // Update all of the monitors
            for (int i = 0; i < monitors.size(); i++)
                monitors.get(i).updateHashingProgress( curProgress, (int)total );
        }
        while ( done < hashers.size() ); // loop until all workers are finished
        
        // Now go through each worker and grab its final hash value
        for (int i=0;i<hashers.size();i++)
        {
            HasherThread ht = hashers.get(i);
            byte[] hash;
            
            try {
                 ht.join(); // sanity check, make sure the workers are done
            } catch ( InterruptedException ie ) { }
            
            hash = ht.getHash();
            
            if ( hash != null && hash.length > 0 ) // make sure the hash was actually calculated
                hashes.add( hash );
        }
        
        duration = Calendar.getInstance().getTimeInMillis() - start;
        
        // Now send the final hashes to all monitors
        for (int i = 0; i < monitors.size(); i++)
            monitors.get(i).finishedHashing( hashes, drives, duration );
    }
    
    public void cancel()
    {
        // Set our global cancel variable
        cancelNow = true;
        
        // Wait for our main thread to finish (it'll wait for all workers first)
        try {
            this.join(1000); // (but don't wait forever)
        } catch ( InterruptedException ie ) { }
    }
    
    private class HasherThread extends Thread {
        private File _Drive;
        public int _Progress = 0;
        public byte[] _Hash = null;
        
        public HasherThread( File f )
        {
            _Drive = f;
        }
        
        public byte[] getHash()
        {
            if ( _Hash != null )
                return _Hash;
            return new byte[0];
        }
        
        public int getProgress()
        {
            return _Progress;
        }
        
        public long getSizeToHash()
        {
            long sizeToHash = 0;
            File part1 = new File( _Drive.getAbsolutePath()+"1" );

            // only do the boot record work if partition 1 exists
            if ( part1.exists() )
            {
                // Read and hash the boot sector
                if ( part1.length() > 0 )
                {
                    sizeToHash = BootSectorSize + part1.length();
                }
                else
                {
                    sizeToHash = _Drive.length();
                    if ( sizeToHash <= 0 )
                        sizeToHash = BootSectorSize + GuessImageSize;
                }
            }
            else
            {
                sizeToHash = _Drive.length();
                if ( sizeToHash <= 0 )
                    sizeToHash = GuessImageSize;
            }
            
            return sizeToHash;
        }
        
        public void run()
        {
            try
            {
                byte[] buff = new byte[BlockSize];
                FileInputStream fin = new FileInputStream( _Drive );
                MessageDigest dgst = MessageDigest.getInstance("SHA-256");
                int len, totalRead = 0, toRead = BlockSize;
                long sizeToHash = getSizeToHash();
                
                while ( (len=fin.read(buff,0,toRead)) > 0 && totalRead < sizeToHash )
                {
                    totalRead += len;
                    
                    toRead = (int)(sizeToHash - totalRead);
                    if ( toRead <= 0 || toRead > BlockSize )
                        toRead = BlockSize;
                    
                    // update the hash
                    dgst.update( buff, 0, len );
                    // update the progress
                    _Progress++;
                    // check for user cancel
                    if ( cancelNow )
                    {
                        fin.close();
                        return;
                    }
                }
                fin.close();
                
                // update our final result hash
                _Hash = dgst.digest();
            } 
            catch ( Throwable t )
            {
                t.printStackTrace();
            }
        }
    }
}

