/**
  * This file is part of VoteBox.
  * 
  * VoteBox is free software: you can redistribute it and/or modify
  * it under the terms of the GNU General Public License version 3 as published by
  * the Free Software Foundation.
  * 
  * You should have received a copy of the GNU General Public License
  * along with VoteBox, found in the root of any distribution or
  * repository containing all or part of VoteBox.
  * 
  * THIS SOFTWARE IS PROVIDED BY WILLIAM MARSH RICE UNIVERSITY, HOUSTON,
  * TX AND IS PROVIDED 'AS IS' AND WITHOUT ANY EXPRESS, IMPLIED OR
  * STATUTORY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, WARRANTIES OF
  * ACCURACY, COMPLETENESS, AND NONINFRINGEMENT.  THE SOFTWARE USER SHALL
  * INDEMNIFY, DEFEND AND HOLD HARMLESS RICE UNIVERSITY AND ITS FACULTY,
  * STAFF AND STUDENTS FROM ANY AND ALL CLAIMS, ACTIONS, DAMAGES, LOSSES,
  * LIABILITIES, COSTS AND EXPENSES, INCLUDING ATTORNEYS' FEES AND COURT
  * COSTS, DIRECTLY OR INDIRECTLY ARISING OUR OF OR IN CONNECTION WITH
  * ACCESS OR USE OF THE SOFTWARE.
 */

package actionparser;

import java.io.*;
import java.util.*;


import sexpression.ASExpression;
import sexpression.stream.*;
import votebox.middle.*;
import votebox.middle.driver.*;
import votebox.middle.view.*;



public class ActionParser {
	
	private ArrayList<UIAction> actions=new ArrayList<UIAction>();
	private ArrayList<PageTranscript> pageViews;
	private HashMap<String, Integer> transitions;
	private Layout layout;
	private int reviewIndex=-1;//page index of review screen
	
	/**
	 * @param inputPath a path to a file to read from
	 * @param config is the path to the ballot config file
	 */
	public void parseFile(String inputPath, String outputPath, String config){
		actions=new ArrayList<UIAction>();
		pageViews=null;
		
		InputStream in=null;
		PrintStream out=null;
		ASEInputStreamReader reader=null;
		ASExpression dat=null;

		//setup input stream
		try{
			in = new FileInputStream(inputPath);
		}catch(FileNotFoundException e){
			System.out.println("Could not find file: "+ inputPath);
			return;
		}
		
		//setup output stream
		try{
			if(outputPath!=null)
				out = new PrintStream(outputPath);
			else
				out=System.out;
		}catch(FileNotFoundException e){
			System.out.println("Could not write to file: "+ outputPath);
		}catch(SecurityException e){
			System.out.println("Security problem:  "+e.getMessage());
		}
		
		reader = new ASEInputStreamReader(in);
		
		//build a list of UIActions
		int availible=0;
		try{
			availible=in.available();
		}catch(IOException e){}
		
		while(availible>0){//TODO can this be done more gracefully?
			try{
				dat=reader.read();
				availible=in.available();
			}
			catch(InvalidVerbatimStreamException e){System.out.println("FAIL: Invalid Verbatim Stream: " + e.getMessage()); break;}
			catch(IOException e){System.out.println("FAIL: IO exception: "+ e.getMessage());}
		
			actions.add(new UIAction(dat));
			
		
		}
		
		//parse layout
		IBallotVars vars=null;
		try{
			 vars = new GlobalVarsReader(config).parse();
			 layout=new LayoutParser().getLayout(vars, 1, "en");
		}catch(Exception e){System.out.println("Exception: "+e.getMessage());}
		
		//Create list of transitions
		transitions=getTransitions();
		
		//Create list of PageTranscripts 
		pageViews=getPageViews(actions, transitions);
		
		//print the detailed page sequence to the specified output stream
		dumpPageSequence(out);
		} 
	

	/**
	 * Search the layout for any page transitions and map the ID to the transition direction
	 * @param layout the layout to search
	 * @return the mapping of IDs to transitions
	 */
	private HashMap<String, Integer> getTransitions(){
		String type="";
		int pagenum=-1;
		HashMap<String, Integer> trans=new HashMap<String, Integer>();
		for(RenderPage page: layout.getPages()){//for each page
			pagenum++;//advance to next page
			
			for(IDrawable item: page.getChildren()){//for each item
				if(item.getProperties().contains("ButtonStrategy")){//item is a button
					try {
						type=item.getProperties().getString("ButtonStrategy");
					} catch (IncorrectTypeException e) {System.out.println("No Strategy...");}
					if(type.equals("NextPage")){
						trans.put(item.getUniqueID(),new Integer(-1));//special encoding for next page

					}
					else if(type.equals("PreviousPage")){
						trans.put(item.getUniqueID(),new Integer(-2));//special encoding for previous page

					}
					else if(type.equals("GoToPageContaining")){
						String loc="";
						try {
							loc=item.getProperties().getString("UID");
						} catch (IncorrectTypeException e) {System.out.println("No UID...");}
						trans.put(item.getUniqueID(),findPageContaining(loc));
					}
					else if(type.equals("CastBallot")){
						trans.put(item.getUniqueID(),new Integer(-3));//special encoding for cast ballot
						reviewIndex=pagenum-1;
					}
					//System.out.println(item.getUniqueID()+" "+type+" "+page.toString());
				}
			}
		}
		return trans;
	}
	
	/**
	 * Finds the page number in the layout contianing the element with the specified UID
	 * @param uid the UID to search for 
	 * @param layout the layout to search in
	 * @return the zero-indexed page number in layout containing uid
	 */
	private Integer findPageContaining(String uid) {
		int pagenum=-1;
		for(RenderPage page: layout.getPages()){//for each page
			pagenum++;//advance to next page
			for(IDrawable item: page.getChildren()){//for each item
					if(item.getUniqueID().compareTo(uid)==0)
						return pagenum;
			}
		}
		return -3;//fail
	}


	/**
	 * parse the UIactions into page views
	 * @param actions the actions to parse
	 * @param trans the transition mapping to use
	 * @return a list of pages transcripts
	 */
	private ArrayList<PageTranscript> getPageViews(ArrayList<UIAction> actions,HashMap<String, Integer> trans){
		
		ArrayList<PageTranscript> pages=new ArrayList<PageTranscript>();
		int pagenum=0, pageviewnum=0;
		PageTranscript p=new PageTranscript(pagenum,pageviewnum);
		
		for(UIAction a:actions){
			p.addAction(a);
			if(trans.containsKey(a.get_UID())&&a.get_action().equals("Selected")){//the item is a page transition and it was selected
				
				pages.add(p);
				pageviewnum++;	

				int temp=trans.get(a.get_UID()).intValue();//the target page
				if(temp==-1)
						pagenum++;
				else if (temp==-2)
						pagenum--;
				else
						pagenum=temp;
				p=new PageTranscript(pagenum,pageviewnum);
				p.addAction(a);//register transition as first event of new page as well
			}
		}
		pages.add(p);
		return pages;
	}
	
	
	/**
	 * prints a detailed CSV report of the page-by-page interactions
	 * 3 output columns: 
	 *    * ordinal number of page view
	 *    * number of the page visited (zero indexed)
	 *    * time spent on the visit (in ms)
	 * @param out the output destination
	 */
	public void dumpPageSequence(PrintStream out){
		for(PageTranscript page: pageViews)
			page.printPageInfo(out);
	}
	
	public long getStartTime(){
		return actions.get(0).get_time();
	}
	
	public long getEndTime(){
		return actions.get(actions.size()-1).get_time();
	}
	
	public long getTotalTime(){
		return getEndTime()-getStartTime();
	}
	
	//return the transcrpt for the first time the specified page is visited
	public PageTranscript getFirstPageView(int page){
		for(PageTranscript p: pageViews)
			if(p.getPageNum()==page)
				return p;
		return null;
	}
		
	//sum of time spent on the page corresponding to the specified page number 
	public long getTotalPageTime(int page){
		long total=0;
		for(PageTranscript p: pageViews)
			if(p.getPageNum()==page)
				total+=p.getTotalTime();
		return total;
	}
	
	//iterate over the page views and count instances matching the desired page number 
	public int getPageViews(int page){
		int count=0;
		for(PageTranscript p: pageViews)
			if(p.getPageNum()==page)
				count++;
		return count;
	}

	public int getReviewPage(){
		return reviewIndex;
	}
	
	/**
	 * @param args
	 */
	public static void main(String[] args) {
		ActionParser ap=new ActionParser();
		
		if(args.length<2){
			System.out.println("ActionParser requires at least two parameters: input-path config-path [output-path]");
			System.exit(1);
		}
		
		ap.parseFile(args[0],(args.length>2)?args[2]:null,args[1]);

	}

}
