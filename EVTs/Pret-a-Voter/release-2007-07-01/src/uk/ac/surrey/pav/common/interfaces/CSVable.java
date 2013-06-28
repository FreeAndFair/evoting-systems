package uk.ac.surrey.pav.common.interfaces;

/**
 * Classes that implement this interface can be turned into a
 * line of comma separated values (CSV).
 * 
 * @author David Lundin
 *
 */
public interface CSVable {

	/**
	 * Returns the comma separated values as a StringBuffer
	 * 
	 * @return CSV of the object
	 */
	public StringBuffer toCSV();
	
}
