/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.soap.response.Statistics.java
  *
  * -----------------------------------------------------------------------
  * 
  *  (c) 2003  Ministerie van Binnenlandse Zaken en Koninkrijkrelaties
  *
  *  Project		: Kiezen Op Afstand (KOA)
  *  Project Number	: ECF-2651
  *  
  *  History:
  *  Version	Date		Name		Reason
  * ---------------------------------------------------------
  *  1.0		29-04-2003	XUi 		First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.soap.response;
import com.logicacmg.koa.soap.response.Counter;
/**
 * Class representing a set of counters
 * 
 * @author X@nder
 *
 */
public class Statistics
{
	Counter[] counters;
	/**
	 * Returns the array of counters
	 * 
	 * @return Counter [] all the counters
	 */
	public Counter[] getCounters()
	{
		return counters;
	}
	/**
	 * Sets the counter array
	 * 
	 * @param counters All the counters
	 */
	public void setCounters(Counter[] counters)
	{
		this.counters = counters;
	}
}