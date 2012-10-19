/**
 * 
 */
package org.scantegrity.common;

import java.io.File;
import java.io.IOException;
import javax.sound.sampled.AudioFormat;
import javax.sound.sampled.AudioInputStream;
import javax.sound.sampled.AudioSystem;
import javax.sound.sampled.Clip;
import javax.sound.sampled.DataLine;
import javax.sound.sampled.LineUnavailableException;
import javax.sound.sampled.UnsupportedAudioFileException;

/**
 * @author jconway
 *
 */
public class AudioFile implements Runnable {
	private String c_fileName; 
	private int c_loopCount; 
	
	public AudioFile(String p_fileName, int p_loopCount) {
		c_fileName = p_fileName; 
		c_loopCount = p_loopCount; 
	}
	
	
	@Override
	public void run() {
		AudioInputStream l_stream = null;
		try {
			l_stream = AudioSystem.getAudioInputStream(new File(c_fileName));
		} catch (UnsupportedAudioFileException e_uaf) {
			System.err.println("Unsupported Audio File");
			return;
		} catch (IOException e1) {
			System.err.println("Could not Open Audio File");
			return;
		}
 
		AudioFormat l_format = l_stream.getFormat();
		Clip l_dataLine = null;
		DataLine.Info l_info = new DataLine.Info(Clip.class, l_format); 
		
		if (!AudioSystem.isLineSupported(l_info)) {
			System.err.println("Audio Line is not supported");
		}
		
		try {
			l_dataLine = (Clip) AudioSystem.getLine(l_info);
		    l_dataLine.open(l_stream);
		} catch (LineUnavailableException ex) {
			System.err.println("Audio Line is unavailable.");
		} catch (IOException e) {
			System.err.println("Cannot playback Audio, IO Exception.");
		}

		l_dataLine.loop(c_loopCount);

		try {
			Thread.sleep(7000);
		} catch (InterruptedException e) {
			System.err.println("Could not sleep the audio player thread.");
		}
		
		l_dataLine.close();
	}

}
