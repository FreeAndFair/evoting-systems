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

import java.io.PrintStream;
import java.util.*;

public class PageTranscript {
	
	private int _pageNum;
	private int _pageViewNum;
	private ArrayList<UIAction> _actions=new ArrayList<UIAction>();
	
	public PageTranscript(int pageNum, int pageViewNum){
		_pageNum=pageNum;
		_pageViewNum=pageViewNum;
	}
	
	public PageTranscript(ArrayList<UIAction> actions,int pageNum, int pageViewNum){
		_actions=actions;
		_pageNum=pageNum;
		_pageViewNum=pageViewNum;
	}
	
	public long getTotalTime(){
		return _actions.get(_actions.size()-1).get_time()-_actions.get(0).get_time();
	}

	/**
	 * @return Returns the _actions.
	 */
	public ArrayList<UIAction> getActions() {
		return _actions;
	}

	/**
	 * @param _actions The _actions to set.
	 */
	public void setActions(ArrayList<UIAction> _actions) {
		this._actions = _actions;
	}
	
	public void addAction(UIAction action){
		_actions.add(action);
	}

	/**
	 * @return Returns the _pageNum.
	 */
	public int getPageNum() {
		return _pageNum;
	}

	/**
	 * @param num The _pageNum to set.
	 */
	public void setPageNum(int num) {
		_pageNum = num;
	}

	/**
	 * @return Returns the _pageViewNum.
	 */
	public int getPageViewNum() {
		return _pageViewNum;
	}

	/**
	 * @param viewNum The _pageViewNum to set.
	 */
	public void setPageViewNum(int viewNum) {
		_pageViewNum = viewNum;
	}
	
	/**
	 * the time this page view began
	 */
	public long getStartTime() {
		return _actions.get(0).get_time();
	}
	
	/**
	 * the time this page view ended
	 */
	public long getEndTime() {
		return _actions.get(_actions.size()-1).get_time();
	}
	
	public void printPageInfo(PrintStream out){
		out.println(getPageViewNum()+","+getPageNum()+","+getTotalTime());
	}
	
}
