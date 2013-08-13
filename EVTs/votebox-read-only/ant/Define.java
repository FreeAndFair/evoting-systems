package ant;

public class Define{
	public String _name = null;
	
	public Define(){}
	
	public Define(String val) {
		this();
		setName(val);
	}

	public void setName(String name){
		_name = name;
	}//setName
	
	public boolean equals(Object define){
		if(!(define instanceof Define))
			return false;
		
		return ((Define)define)._name.equals(_name);
	}//equals
}