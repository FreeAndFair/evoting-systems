/** -----------------------------------------------------------------------
  *
  *   com.logicacmg.koa.scheduler.SchedulerConstants.java
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
  *  0.1		25-04-2003	MKu			First implementation
  * -----------------------------------------------------------------------
  */
package com.logicacmg.koa.scheduler;
/**
 * All constant values for the scheduler
 * 
 * @author KuijerM
 */
public class SchedulerConstants
{
	public final static String STATUS_SCHEDULED = "SCHEDULED";
	public final static String STATUS_PROCESSING = "PROCESSING";
	public final static String STATUS_PROCESSED = "PROCESSED";
	public final static String STATUS_ABORTED = "ABORTED";
	public final static String INIT_ERROR_MESSAGE =
		"An error accured while initializing the Job";
	public final static String ACTION_DELETE = "DELETE";
	public final static String ACTION_NEW = "NEW";
	public final static String ACTION_COLLECT_COUNTERS = "collectcounters";
	public final static String JOB_TYPE_ID_COLLECT_COUNTERS = "100";
	public final static String JOB_TYPE_ID_IMPORT_KIES_LIJST = "200";
	public final static String JOB_TYPE_ID_IMPORT_KIES_REGISTER = "300";
	public final static String JOB_TYPE_ID_REMOVE_KIES_LIJST = "400";
	public final static String JOB_TYPE_ID_REMOVE_KIES_REGISTER = "500";
	public final static String DATE_FORMAT = "dd-MM-yyyy";
	public final static String DATE_TIME_FORMAT = "dd-MM-yyyy HH:mm";
	public final static int MAX_RESULTS = 100;
	public static final String TEMP_DATA_ID_KEY = "temp_data_id";
}