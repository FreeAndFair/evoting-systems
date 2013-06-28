/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.dataobjects.AbstractAdministrationObject.java
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
  *  0.1		28-04-2003	MKu	        First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.dataobjects;
import java.io.Serializable;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import com.logicacmg.koa.utils.KOALogHelper;
/**
 * Abstract administration object used as base class for 
 * all scheduler related administration objects
 * 
 * @author KuijerM
 * 
 */
public abstract class AbstractAdministrationObject implements Serializable
{
	/* Variables */
	protected String overviewJSP = null;
	protected String detailJSP = null;
	protected int pageNo = 1;
	protected boolean isTruncated = false;
	protected final Vector objects = new Vector();
	protected final Hashtable objectsByKey = new Hashtable();
	/* abstract methods that must be implemented by child classes */
	/**
	 * Load objects from a datasource to a vector containing
	 * current data objects.<br>
	 * Method is abstract and must be implemented by all subclasses.
	 * 
	 */
	abstract protected void loadObjects();
	/**
	 * Updates the object with the specified key from the 
	 * underlaying datasource<br>
	 * Method is abstract and must be implemented by all subclasses.
	 * 
	 * @param key The key for the object to update.
	 * 
	 */
	abstract public void updateObject(String key);
	/**
	 * Disables the object with the specified key from the 
	 * underlaying datasource<br>
	 * Method is abstract and must be implemented by all subclasses.
	 * 
	 * @param key The key of the object to disable.
	 * 
	 */
	abstract public void disableObject(String key);
	/**
	 * Refresh all the dataobjects
	 * from the underlaying datasource.
	 * 
	 */
	public void search()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[AbstractAdministrationObject] Clearing stored contents and calling implementation");
		objects.removeAllElements();
		objectsByKey.clear();
		loadObjects();
	}
	/**
	 * Gets the object that is related to the specified key
	 * 
	 * @param key the key to get the object for
	 * 
	 * @return Object the object to retrieve
	 * 
	 */
	public Object getObjectByKey(Object key)
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[AbstractAdministrationObject] Returning object");
		return objectsByKey.get(key);
	}
	/**
	 * Gets the JSP url for the overview page
	 * 
	 * @return String the overview page url
	 * 
	 */
	public String getOverviewJSP()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[AbstractAdministrationObject] Returning overview page");
		return overviewJSP;
	}
	/**
	 * Gets the JSP url for the details page
	 * 
	 * @return String the details page url
	 * 
	 */
	public String getDetailJSP()
	{
		KOALogHelper.log(
			KOALogHelper.TRACE,
			"[AbstractAdministrationObject] Returning detail page");
		return detailJSP;
	}
	/**
	 * Checks if there are no elements in the objects collection
	 * 
	 * @return boolean true if it is empty, false if there are objects
	 * 
	 */
	public boolean isEmpty()
	{
		return objects == null || objects.size() == 0;
	}
	/**
	 * Checks if the search is truncated and there where more 
	 * results then the max number indicates
	 * 
	 * @return boolean indicating if it was a truncated search (true) or not (false)
	 * 
	 */
	public boolean isTruncatedSearch()
	{
		return isTruncated;
	}
	/**
	 * Gets the number of elements that is returned
	 * 
	 * @return int the number of records
	 * 
	 */
	public int getResultCount()
	{
		return objects.size();
	}
	/** 
	 * This method returns a subset of the searchresult, specified by the parameters.
	 * 
	 * @param batchSize Size of the subset
	 * @param batchNumber Specifies the batch number, starting at 0.
	 * @author JvG
	 */
	public Enumeration getResultSubSet(int batchSize, int batchNumber)
	{
		return new SearchResultEnumerator(batchNumber * batchSize, batchSize);
	}
	/** 
	 * Subclass to return a subset of the total search result of the containing search class.
	 * @author JvG
	 */
	class SearchResultEnumerator implements Enumeration
	{
		/** 
		 * offset and len specify the interval to show: [offset ... offset+len-1]
		 */
		private int offset, len;
		/** cursor contains the index of the NEXT item that is to be shown.
		 */
		private int cursor;
		SearchResultEnumerator(int offset, int len)
		{
			this.offset = offset;
			this.len = len;
			this.cursor = offset;
		}
		/**
		 * Method returns object at current cursor and updates cursor.
		 */
		public Object nextElement()
		{
			Object obj = objects.elementAt(cursor);
			cursor++;
			return obj;
		}
		/**
		 * Method returns true if cursor is in current batch 
		 * AND cursor does not exceed resultset size.
		 */
		public boolean hasMoreElements()
		{
			return (cursor < offset + len && objects.size() > cursor);
		}
	}
}
