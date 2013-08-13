package ant;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.Task;

/**
 * Ant task for simple pre-processing.
 * 
 * Supports: #define VALUE
 *           #ifdef VALUE
 *           #ifndef VALUE
 *           #endif
 *           
 * Usage:
 *   <taskdef name="preprocess" classname="ant.PreProcesorTask" classpath="..."/>
 *   <typedef name="define" classname="ant.Define" classpath="..."/>
 *   ...
 *   <preprocess rootdirectory="..." destdirectory="..." filepattern="*.java" debug="yes/no">
 *   	<define name="EVIL"/>
 *   </preprocess>
 * @author Montrose
 *
 */
public class PreProcessorTask extends Task{
	private List<Define> _defined = new ArrayList<Define>();
	private File _root = null;
	private File _dest = null;
	private String _debug = "no";
	
	public PreProcessorTask(){}//PreProcessorTask
	
	public void addDefine(Define define){
		_defined.add(define);
	}//addDefine
	
	public void setRootDirectory(File file){
		_root = file;
	}//setRootDirectory
	
	public void setDestDirectory(File file){
		_dest = file;
	}//setDestDirectory
	
	public void setDebug(String debug){
		_debug = debug;
	}//setDebug
	
	public void execute() throws BuildException{
		if(_root == null || _dest == null)
			throw new BuildException("Expected BOTH RootDirectory and DestDirectory to be set.");
		
		if(!_root.exists())
			throw new BuildException("RootDirectory does not exist");
		
		if(!_dest.exists())
			_dest.mkdirs();
		
		List<File> files = new ArrayList<File>();
		List<File> directories = new ArrayList<File>();
		
		boolean debug = _debug.equals("yes");
		
		directories.add(_root);
		
		while(directories.size() > 0){
			File inQ = directories.remove(0);
			
			//Skip "hidden" directories, unix style
			if(inQ.getName().startsWith("."))
				continue;
			
			if(!debug){
				makeCopy(inQ, _root, _dest, true);
			}else
				log("Created directory for: "+inQ);
			
			for(File subF : inQ.listFiles())
				if(subF.isDirectory())
					directories.add(subF);
				else
					files.add(subF);
		}//while
		
		for(File toProc : files){
			try{
				if(debug)
					log("Finished with: "+toProc.getName());
				else{

					File file = makeCopy(toProc, _root, _dest, false);
					
					if(file != null){
						byte[] data = null;
						
						if(file.getName().endsWith(".java"))
							data = proc(toProc);
						else
							data = read(toProc);

						OutputStream stream = new FileOutputStream(file);
						stream.write(data);
						stream.flush();
						stream.close();
					}//if
				}//if
			}catch (FileNotFoundException e) {
				throw new BuildException(e);
			} catch (IOException e) {
				throw new BuildException(e);
			}
		}//for
	}//execute
	
	private boolean isDefined(Define d){
		for(Define defined : _defined)
			if(defined.equals(d))
				return true;
		
		return false;
	}
	
	public byte[] read(File toProc){
		try{
			InputStream in = new FileInputStream(toProc);
			byte[] buffer = new byte[4 * 1024];
			
			List<byte[]> data = new ArrayList<byte[]>();
			
			int len = -1;
			int size = 0;
			while((len = in.read(buffer)) != -1){
				byte[] b = new byte[len];
				for(int i = 0; i < len; i++)
					b[i] = buffer[i];
				
				data.add(b);
				
				size+=len;
			}//while
			
			byte[] total = new byte[size];
			int i = 0;
			
			for(byte[] b : data){
				System.arraycopy(b, 0, total, i, b.length);
				i += b.length;
			}//for
			
			return total;
		}catch(Exception e){
			throw new BuildException(e);
		}
	}
	
	@SuppressWarnings("deprecation")
	public byte[] proc(File toProc) {
		try{
			List<List<Integer>> lineBreaks = new ArrayList<List<Integer>>();
			
			InputStream in = new FileInputStream(toProc);
			StringBuilder total = new StringBuilder(4 * 1024);
			byte[] buffer = new byte[4* 1024];
			int len = -1;
			
			while((len = in.read(buffer)) != -1){
				total.append(new String(buffer, 0, len));
			}//while
			
			int start = 0;
			int stop = 0;
			
			while(stop < total.length()){
				if(total.charAt(stop) == '\n'){
					List<Integer> pair = new ArrayList<Integer>();
					pair.add(start);
					pair.add(stop+1);
					
					lineBreaks.add(pair);
					
					start = stop+1;
					stop = start;
					
					continue;
				}//if
				
				stop++;
			}//while
			
			//In the normal case where the file doesn't end with a line break...
			if(lineBreaks.get(lineBreaks.size() - 1).get(1) != total.length()){
				List<Integer> pair = new ArrayList<Integer>();
				pair.add(start);
				pair.add(total.length());
				
				lineBreaks.add(pair);
			}//if
			
			Stack<Boolean> copy = new Stack<Boolean>();
			copy.push(true);
			
			StringBuilder newTotal = new StringBuilder(4 * 1024);
			
			for(List<Integer> pair : lineBreaks){
				int startSub = pair.get(0);
				int stopSub = pair.get(1);
				
				String line = total.substring(startSub, stopSub);
				
				String simple = simplify(line);
				
				if(simple.toLowerCase().equals("//#endif")){
					copy.pop();
					newTotal.append("\n");
					continue;
				}//if
				
				if(!copy.peek()){
					newTotal.append("\n");
					continue;
				}//if
				
				if(simple.toLowerCase().startsWith("//#ifdef ")){
					String val = simple.substring(9);
					if(isDefined(new Define(val)))
						copy.push(true);
					else
						copy.push(false);
					
					newTotal.append("\n");
					
					continue;
				}//if
				
				if(simple.toLowerCase().startsWith("//#ifndef ")){
					String val = simple.substring(10);
					if(isDefined(new Define(val)))
						copy.push(false);
					else
						copy.push(true);
					
					newTotal.append("\n");
					
					continue;
				}//if
				
				if(simple.toLowerCase().startsWith("//#define ")){
					String val = simple.substring(10);
					
					_defined.add(new Define(val));
					
					newTotal.append("\n");
					continue;
				}//if
				
				newTotal.append(line);
			}//for
			
			return newTotal.toString().getBytes();
		}catch(IOException e){
			throw new BuildException("Failed processing file: "+toProc, e);
		}//catch
	}//proc

	public String simplify(String line){
		String newline = line.trim();
		
		if(newline.startsWith("//")){
			newline = "//" + newline.substring(2).trim();
		}else
			return line;
		
		if(!newline.startsWith("//#"))
			return line;
		
		if(newline.length() == 3 || Character.isWhitespace(newline.charAt(3)))
			return line;
		
		int i = newline.indexOf(' ');
		if(i == -1)
			return newline;
		
		newline = newline.substring(0, i) + ' ' + newline.substring(i).trim();
		
		return newline;
	}//simplify
	
	private File makeCopy(File current, File parent, File newParent, boolean asDir){
		if(current.getAbsolutePath().startsWith(newParent.getAbsolutePath()))
			return null;
		
		try{
			String cAbs = current.getAbsolutePath();
			String pAbs = parent.getAbsolutePath();

			String newComp = cAbs.substring(pAbs.length());

			if(newComp.length() == 0) return null;

			File newFile = new File(newParent.getAbsolutePath() + newComp);

			if(asDir){
				newFile.mkdirs();
				return newFile;
			}else{
				newFile.createNewFile();
				return newFile;
			}//if

		}catch(IOException e){
			throw new BuildException("Failed create copy of File", e);
		}
	}//makeCopy
}//PreProcessorTask