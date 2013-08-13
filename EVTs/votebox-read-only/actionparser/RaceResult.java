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


import java.util.ArrayList;
import java.util.Iterator;

import sexpression.ASExpression;
import sexpression.StringExpression;
import sexpression.ListExpression;

/**
 * Class for representing race results (as extracted from a log of a VoteBox session).
 * 
 * @author Montrose
 *
 */
public class RaceResult {
	private String _UID;
	private ArrayList<String> _res;
	
	/**
	 * Extracts a list of RaceResults from the given SExpression
	 * 
	 * @param sexp - SExpression in question.
	 * @return extracted list
	 */
	public static ArrayList<RaceResult> parseRaces(ASExpression sexp){
		ListExpression list=null;
		
		ArrayList<RaceResult>res=new ArrayList<RaceResult>();
		
		try{
			list=(ListExpression)sexp;
		}catch(ClassCastException e){
			System.out.println("Invalid UIAction S-Expression");
			System.exit(1);
		}
		
		Iterator<ASExpression> it=list.iterator();
		while(it.hasNext()){//for each race
			ASExpression aex = it.next();
			ListExpression ex=(ListExpression)aex;
			RaceResult rr=new RaceResult();
			
			Iterator raceIt=ex.iterator();
				
			String raw=((StringExpression)(raceIt.next())).toString();
			rr.set_UID(raw);//get the race id

		//	System.out.println("***"+rr.get_UID()+"***");
			
			ArrayList<String>votes=new ArrayList<String>();
			
			
			Iterator voteIt=((ListExpression)raceIt.next()).iterator();
			if(voteIt.hasNext()==false)
					votes.add("(none)");
			while(voteIt.hasNext()){//for each selected candidate
				String v=((StringExpression)(voteIt.next())).toString();
				votes.add(v);
				
				//System.out.println(v.substring(1, v.length()-1));
			}
			
			rr.set_res(votes);//get the selected candidates
			res.add(rr);
			
		}
		return res;
	}
	
	/**
	 * Constrcts a new RaceResult
	 * @param uid - wit this UID
	 * @param res - and this list of results
	 */
	public RaceResult(String uid, ArrayList<String> res){
		_UID=uid;
		_res=res;
	}
	
	/**
	 * Constructs an empty (uninitialized) RaceResult.
	 *
	 */
	public RaceResult(){
		_UID=null;
		_res=null;
	}
	/**
	 * @return the _res
	 */
	public ArrayList<String> get_res() {
		return _res;
	}
	
	/**
	 * adds an entry to the results
	 */
	public void add_res(String res){
		_res.add(res);
	}

	/**
	 * @param _res the _res to set
	 */
	public void set_res(ArrayList<String> _res) {
		this._res = _res;
	}

	/**
	 * @return the _UID
	 */
	public String get_UID() {
		return _UID;
	}

	/**
	 * @param _uid the _UID to set
	 */
	public void set_UID(String _uid) {
		_UID = _uid;
	}

	/**
	 * @return a String representation of this RaceResult
	 */
	public String toString(){
		String res= "UID: "+_UID + " (";
		for(String item: _res)
				res+=item +" ";
		res+=")";
		return res;
	}
}
