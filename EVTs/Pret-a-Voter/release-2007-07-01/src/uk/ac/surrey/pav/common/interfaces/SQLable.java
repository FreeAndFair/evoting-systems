package uk.ac.surrey.pav.common.interfaces;

/**
 * Classes that implement this interface can easily be turned into SQL statements
 * for insertion into a MySQL or MySQL compliant database.
 * 
 * @author David Lundin
 *
 */
public interface SQLable {
	
	public StringBuffer toSQL();

}
