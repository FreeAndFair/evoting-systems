package uk.ac.surrey.pav.administrator;

/**
 * An entity that can have its name changed
 * 
 * @author David Lundin
 *
 */
public interface NameEditableEntity {
	
	public String getName();
	
	public void setName(String name);

}
